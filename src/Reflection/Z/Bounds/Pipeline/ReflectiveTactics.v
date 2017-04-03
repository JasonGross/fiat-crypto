(** * Reflective Pipeline: Tactics that execute the pipeline *)
(** N.B. This file should not need to be changed in normal
    modifications of the reflective transformations; to modify the
    transformations performed in the reflective pipeline; see
    Pipeline/Definition.v.  If the input format of the pre-reflective
    goal changes, prefer adding complexity to Pipeline/Glue.v to
    transform the goal and hypotheses into a uniform syntax to
    modifying this file.  This file will need to be modified if you
    perform heavy changes in the shape of the generic or ℤ-specific
    reflective machinery itself, or if you find bugs or slowness. *)
(** ** Preamble *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.WfReflective.
Require Import Crypto.Reflection.RenameBinders.
Require Import Crypto.Reflection.Eta.
Require Import Crypto.Reflection.EtaInterp.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Z.Syntax.Util.
Require Import Crypto.Reflection.Z.Bounds.Interpretation.
Require Import Crypto.Reflection.Z.Bounds.Relax.
Require Import Crypto.Reflection.Reify.
Require Import Crypto.Reflection.Z.Reify.
Require Import Crypto.Reflection.Z.Bounds.Pipeline.OutputType.
Require Import Crypto.Reflection.Z.Bounds.Pipeline.Definition.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.SubstLet.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Util.Option.
Require Import Bedrock.Word.

(** The final tactic in this file, [do_reflective_pipeline], takes a
    goal of the form
<<
@Bounds.is_bounded_by (codomain T) bounds (fZ (cast_back_flat_const v))
  /\ cast_back_flat_const fW = fZ (cast_back_flat_const v)
>>

    where [fW] must be a context definition which is a single evar,
    and all other terms must be evar-free.  It fully solves the goal,
    instantiating [fW] with an appropriately-unfolded
    (reflection-definition-free) version of [fZ (cast_back_flat_const
    v)] which has been transformed by the reflective pipeline. *)

Module Export Exports.
  Export Crypto.Reflection.Reify. (* export for the instances for recursing under binders *)
  Export Crypto.Reflection.Z.Reify. (* export for the tactic redefinitions *)
  Export Crypto.Reflection.Z.Bounds.Pipeline.Definition.Exports.
End Exports.

(** ** Pre-reification *)
(** The [assert_reflective] tactic is the first one that gets run, and
    it takes a goal of the form
<<
@Bounds.is_bounded_by (codomain T) bounds _
  /\ cast_back_flat_const fW = fZ (cast_back_flat_const v)
>>
    where [fW] must be a context variable.  It creates a second goal
    of the form [{ rexpr | forall x, Interp _ rexpr x = fZ x }], which
    is what reification works on.  This goal is placed first, and in
    the second (original) subgoal, [fZ] is replaced with the
    interpretation of the evar which will be filled with the reflected
    constant. *)
Ltac assert_reflective :=
  lazymatch goal with
  | [ |- @Bounds.is_bounded_by (codomain ?T) ?bounds _
         /\ cast_back_flat_const ?fW = ?fZ (cast_back_flat_const ?v) ]
    => let rexpr := fresh "rexpr" in
       simple refine (let rexpr : { rexpr | forall x, Interp interp_op (t:=T) rexpr x = fZ x } := _ in _);
       [ cbv [interp_flat_type interp_base_type Tuple.tuple Tuple.tuple'] in *;
         subst fW
       | rewrite <- (proj2_sig rexpr);
         let rexpr' := fresh rexpr in
         set (rexpr' := proj1_sig rexpr);
         unfold proj1_sig in rexpr';
         subst rexpr fZ ]
  end.

(** ** Reification *)
(** The [rexpr_cbv] tactic unfolds various constants in a goal of the
    form
<<
{ rexpr | forall x, Interp _ rexpr x = f x }
>>
    to get the goal into a form that [eexists; Reify_rhs] can handle.
    This tactic is somewhat more general than it currently needs to
    be; it can handle cases where [f] is already unfolded, cases
    where [f] is a definition or a context variable, and cases where
    [f] is some sort of uncurrying functional applied to a context
    variable, definition, or unfolded term.  In the old pipeline, it
    needed to handle all of these cases. *)
Ltac rexpr_cbv :=
  lazymatch goal with
  | [ |- { rexpr | forall x, Interp _ (t:=?T) rexpr x = ?uncurry ?oper x } ]
    => let operf := head oper in
       let uncurryf := head uncurry in
       try cbv delta [T]; try cbv delta [oper];
       try cbv beta iota delta [uncurryf]
  | [ |- { rexpr | forall x, Interp _ (t:=?T) rexpr x = ?oper x } ]
    => let operf := head oper in
       try cbv delta [T]; try cbv delta [oper]
  end;
  cbv beta iota delta [interp_flat_type interp_base_type].
(** The [reify_sig] tactic handles a goal of the form
<<
{ rexpr | forall x, Interp _ rexpr x = f x }
>>
    by reifying [f]. *)
Ltac reify_sig :=
  rexpr_cbv; eexists; Reify_rhs; reflexivity.
(** The [do_reify] tactic runs [reify_sig] on the first goal, and
    then, in the second goal left by [assert_reflective], reduces
    projections of the reified pair (which was an evar, and is now
    instantiated). *)
Ltac do_reify := [ > reify_sig | cbv beta iota in * ].

(** ** Post-reification, pre-Wf transformations *)
(** The [do_pre_wf_pipeline] tactic runs the part of the pipeline,
    defined in Pipeline.Definition, which does not rely on
    well-foundedness.  It operates on a goal of the form
<<
Bounds.is_bounded_by bounds (Interp _ fZ v')
  /\ cast_back_flat_const fW = Interp _ fZ v'
>>
    where [fZ] is expected to be a context variable, and does not
    change the shape of the goal (it updates the definition of [fZ]). *)
Ltac do_pre_wf_pipeline :=
  lazymatch goal with
  | [ |- Bounds.is_bounded_by ?bounds (Interp _ ?fZ ?v')
         /\ cast_back_flat_const ?fW = Interp _ ?fZ ?v' ]
    => rewrite <- !(InterpPreWfPipeline fZ);
       let fZ' := fresh fZ in
       rename fZ into fZ';
       set (fZ := PreWfPipeline fZ');
       vm_compute in fZ; clear fZ'
  end.

(** ** Well-foundedness *)
(** The [assert_wf] tactic adds an opaque hypothesis of type [Wf fZ]
    to the context, pulling [fZ] from a goal of the form
<<
Bounds.is_bounded_by _ _ /\ cast_back_flat_const fW = Interp _ fZ _
>>
 *)
Ltac prove_rexpr_wfT
  := reflect_Wf Equality.base_type_eq_semidec_is_dec Equality.op_beq_bl.
Ltac assert_wf :=
  lazymatch goal with
  | [ |- Bounds.is_bounded_by _ _ /\ cast_back_flat_const ?fW = Interp _ ?fZ _ ]
    => assert (Wf fZ) by (clear; prove_rexpr_wfT)
  end.

(** ** Post-Wf pipeline *)
Notation rexpr_post_wf_pipeline_option rexprZ rexpr_bounds
  := (PostWfPipeline rexprZ rexpr_bounds)
       (only parsing).
Notation rexpr_post_wf_pipeline_postprocess1 v
  := (invert_Some v)
       (only parsing).
Notation get_output_type v := (OutputType v) (only parsing).
Notation get_bounds v := (@output_bounds v) (only parsing).
Notation get_output_expr v := (@output_expr v) (only parsing).
Notation rexpr_post_wf_pipeline_postprocess2 v
  := (renamify v)
       (only parsing).

Notation rexpr_correct_and_bounded rexprZ rexprW input_bounds output_bounds rexprZ_Wf
  := (fun v v' Hv
      => proj2
           (@PostWfPipelineCorrect
              _ rexprZ input_bounds rexprZ_Wf
              output_bounds rexprW
              _
              v v' Hv))
       (only parsing).

Ltac rexpr_correct_and_bounded_obligation_tac :=
  intros; subst_let; clear;
  lazymatch goal with
  | [ |- ?x = Some ?y ]
    => abstract vm_cast_no_check (eq_refl (Some y))
  | _ => vm_compute; constructor
  end.


Ltac make_correctness rexprZ bounds Hcorrectness :=
  let rexprW_pkgo := (eval vm_compute in (rexpr_post_wf_pipeline_option rexprZ bounds)) in
  let rexprW_pkg := (eval vm_compute in (rexpr_post_wf_pipeline_postprocess1 rexprW_pkgo)) in
  let rexprT := constr:(get_output_type rexprW_pkg) in
  let rexprW' := (eval vm_compute in (get_output_expr rexprW_pkg)) in
  let rexprW := (eval cbv beta iota zeta in (rexpr_post_wf_pipeline_postprocess2 rexprW')) in
  let rexpr_output_bounds := (eval vm_compute in (get_bounds rexprW_pkg)) in
  let rexprZ_Wf := lazymatch goal with H : Wf rexprZ |- _ => H end in
  simple refine (let Hcorrectness := rexpr_correct_and_bounded rexprZ rexprW bounds rexpr_output_bounds rexprZ_Wf in _);
  [ rexpr_correct_and_bounded_obligation_tac.. | clearbody Hcorrectness ].
Ltac do_pose_correctness Hcorrectness :=
  lazymatch goal with
  | [ |- @Bounds.is_bounded_by (codomain ?T) ?bounds _
         /\ cast_back_flat_const ?fW = Interp _ ?fZ (@cast_back_flat_const _ _ _ ?input_bounds ?v) ]
    => make_correctness fZ input_bounds Hcorrectness
  end.
Ltac pretighten_bounds tighter_bounds :=
  lazymatch goal with
  | [ |- @Bounds.is_bounded_by ?t ?relaxed_bounds _ /\ cast_back_flat_const ?v = ?k ]
    => simple refine (@relax_output_bounds t tighter_bounds relaxed_bounds _ v k _ _)
  end.
Ltac posttighten_bounds :=
  [ > clear; vm_compute; reflexivity | unfold eq_rect | clear; abstract vm_cast_no_check (eq_refl true) ].
Ltac pretighten_bounds_from_correctness Hcorrectness :=
  cbv beta iota zeta in Hcorrectness;
  lazymatch type of Hcorrectness with
  | forall v v', _ -> Bounds.is_bounded_by ?tighter_bounds _ /\ _
    => pretighten_bounds tighter_bounds
  end.
Ltac tighten_bounds_from_correctness Hcorrectness :=
  pretighten_bounds_from_correctness Hcorrectness; posttighten_bounds.

Declare Reduction interp_red := cbv [Interp InterpEta interp_op interp interp_eta interpf interpf_step interp_flat_type_eta interp_flat_type_eta_gen SmartMap.SmartFlatTypeMap codomain domain interp_flat_type interp_base_type SmartMap.smart_interp_flat_map lift_op Zinterp_op SmartMap.SmartFlatTypeMapUnInterp SmartMap.SmartFlatTypeMapInterp2 fst snd cast_const ZToInterp interpToZ].
(* hopefully separating this out into a separate tactic will make it
   show up in the Ltac profile *)
Ltac clear_then_abstract_reflexivity x :=
  clear; abstract exact_no_check (eq_refl x).
Ltac specialize_Hcorrectness Hcorrectness :=
  lazymatch goal with
  | [ |- @Bounds.is_bounded_by (codomain ?T) ?bounds (Interp _ ?fZ ?v')
         /\ cast_back_flat_const ?fW = Interp _ ?fZ ?v' ]
    => let v := lazymatch v' with cast_back_flat_const ?v => v end in
       specialize (Hcorrectness v' v);
       lazymatch type of Hcorrectness with
       | ?T -> Bounds.is_bounded_by _ _
               /\ cast_back_flat_const (@Interp ?base_type ?interp_base_type ?op ?interp_op ?fWT ?fW' ?args) = _
         => cut T;
            [ (let H := fresh in intro H; specialize (Hcorrectness H); clear H);
              rewrite <- (@eq_InterpEta base_type interp_base_type op interp_op fWT fW' args) in Hcorrectness
            | ]
       end;
       [ lazymatch type of Hcorrectness with
           Bounds.is_bounded_by _ _ /\ cast_back_flat_const ?fW' = _
           => let fWev := (eval cbv delta [fW] in fW) in
              let fW'_orig := fW' in
              let fW' := (eval interp_red in fW') in
              let fW' := (eval extra_interp_red in fW') in
              let fW' := lazymatch do_constant_simplification with
                         | true => (eval constant_simplification in fW')
                         | _ => fW'
                         end in
              unify fWev fW';
              replace fW with fW'_orig by clear_then_abstract_reflexivity fW
         end
       | ]
  end.
Ltac handle_bounds_from_hyps :=
  repeat match goal with
         | _ => assumption
         | [ |- cast_back_flat_const _ = cast_back_flat_const _ ] => reflexivity
         | [ |- _ /\ _ ] => split
         | [ |- Bounds.is_bounded_by (_, _) _ ] => split
         end.
Ltac do_post_wf_pipeline :=
  let Hcorrectness := fresh "Hcorrectness" in
  do_pose_correctness Hcorrectness;
  tighten_bounds_from_correctness Hcorrectness;
  specialize_Hcorrectness Hcorrectness;
  [ exact Hcorrectness
  | handle_bounds_from_hyps ].

(** ** The Entire Pipeline *)
(** The [do_reflective_pipeline] tactic solves a goal of the form that
    is described at the top of this file, and is the public interface
    of this file. *)
Ltac do_reflective_pipeline :=
  assert_reflective;
  do_reify;
  do_pre_wf_pipeline;
  assert_wf;
  do_post_wf_pipeline.
