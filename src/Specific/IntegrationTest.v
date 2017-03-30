Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Algebra.
Require Import Crypto.NewBaseSystem.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Specific.NewBaseSystemTest.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.Tuple Crypto.Util.Sigma Crypto.Util.Notations Crypto.Util.ZRange Crypto.Util.BoundedWord.
Import ListNotations.

Require Import Crypto.Reflection.Z.Bounds.Pipeline.Glue.
Require Import Crypto.Reflection.Z.Bounds.Pipeline.Definition.

Section BoundedField25p5.
  Local Coercion Z.of_nat : nat >-> Z.

  Let limb_widths := Eval vm_compute in (List.map (fun i => Z.log2 (wt (S i) / wt i)) (seq 0 10)).
  Let length_lw := Eval compute in List.length limb_widths.

  Local Notation b_of exp := {| lower := 0 ; upper := 2^exp + 2^(exp-3) |}%Z (only parsing). (* max is [(0, 2^(exp+2) + 2^exp + 2^(exp-1) + 2^(exp-3) + 2^(exp-4) + 2^(exp-5) + 2^(exp-6) + 2^(exp-10) + 2^(exp-12) + 2^(exp-13) + 2^(exp-14) + 2^(exp-15) + 2^(exp-17) + 2^(exp-23) + 2^(exp-24))%Z] *)
  (* The definition [bounds_exp] is a tuple-version of the
     limb-widths, which are the [exp] argument in [b_of] above, i.e.,
     the approximate base-2 exponent of the bounds on the limb in that
     position. *)
  Let bounds_exp : Tuple.tuple Z length_lw
    := Eval compute in
        Tuple.from_list length_lw limb_widths eq_refl.
  Let bounds : Tuple.tuple zrange length_lw
    := Eval compute in
        Tuple.map (fun e => b_of e) bounds_exp.

  Let feZ : Type := tuple Z 10.
  Let feW : Type := tuple word32 10.
  Let feBW : Type := BoundedWord 10 32 bounds.
  Let phi : feBW -> F m :=
    fun x => B.Positional.Fdecode wt (BoundedWordToZ _ _ _ x).

  (* TODO : change this to field once field isomorphism happens *)
  Definition add :
    { add : feBW -> feBW -> feBW
    | forall a b, phi (add a b) = F.add (phi a) (phi b) }.
  Proof.
    lazymatch goal with
    | [ |- { f | forall a b, ?phi (f a b) = @?rhs a b } ]
      => apply lift2_sig with (P:=fun a b f => phi f = rhs a b)
    end.
    intros. eexists ?[add]. cbv [phi].
    rewrite <- (proj2_sig add_sig).
    symmetry; rewrite <- (proj2_sig carry_sig); symmetry.
    set (carry_addZ := fun a b => proj1_sig carry_sig (proj1_sig add_sig a b)).
    change (proj1_sig carry_sig (proj1_sig add_sig ?a ?b)) with (carry_addZ a b).
    cbv beta iota delta [proj1_sig add_sig carry_sig runtime_add runtime_and runtime_mul runtime_opp runtime_shr sz] in carry_addZ.
    cbn beta iota delta [fst snd] in carry_addZ.
    apply f_equal.
    (* jgross start here! *)
    refine_to_reflective_glue.

    Require Import Crypto.Util.LetIn.
    Require Import Crypto.Reflection.Z.Syntax.Util.
    Require Import Crypto.Util.Tactics.Head.
    Require Import Crypto.Util.Curry.
    Require Import Crypto.Util.Tactics.ETransitivity.
    Require Import Crypto.Reflection.Syntax.
    Require Import Crypto.Reflection.Z.Syntax.
    Require Import Crypto.Reflection.Reify.
    Require Import Crypto.Reflection.Z.Bounds.Interpretation.
    Require Import Crypto.Reflection.Z.Reify.
    Require Import Crypto.Reflection.Z.Bounds.Relax.
    Require Import Crypto.Reflection.Z.MapBounds.
    Require Import Crypto.Reflection.Z.MapBoundsInterp.
    Require Import Crypto.Reflection.Linearize.
    Require Import Crypto.Reflection.Z.MapBoundsInterp.
    Require Import Crypto.Reflection.Eta.
    Require Import Crypto.Reflection.LinearizeInterp.
    Require Import Crypto.Reflection.EtaInterp.
    Require Import Crypto.Reflection.RenameBinders.
    Require Import Crypto.Reflection.Wf.
    Require Import Crypto.Util.Option.
    Require Import Crypto.Reflection.WfReflective.
    Require Import Crypto.Reflection.SmartMap.
    Require Import Crypto.Reflection.Z.ArithmeticSimplifier.
    Require Import Crypto.Reflection.Z.ArithmeticSimplifierInterp.
    Require Import Crypto.Util.Tactics.SubstLet.

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
Ltac reify_sig :=
  rexpr_cbv; eexists; Reify_rhs; reflexivity.
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
Ltac prove_rexpr_wfT
  := reflect_Wf Equality.base_type_eq_semidec_is_dec Equality.op_beq_bl.

Ltac assert_wf :=
  lazymatch goal with
  | [ |- @Bounds.is_bounded_by (codomain ?T) ?bounds _
         /\ cast_back_flat_const ?fW = Interp _ ?fZ (@cast_back_flat_const _ _ _ ?input_bounds ?v) ]
    => assert (Wf fZ) by (clear; prove_rexpr_wfT)
  end.

Notation rexpr_select_word_sizes_option rexprZ rexpr_bounds
  := (Z.MapBounds.MapBoundsPackaged rexprZ rexpr_bounds)
       (only parsing).
Notation rexpr_select_word_sizes_postprocess1 v
  := (invert_Some v)
       (only parsing).
Notation get_output_type v := (MapBoundsOutputType v) (only parsing).
Notation get_bounds v := (@output_bounds v) (only parsing).
Notation get_output_expr v := (@output_expr v) (only parsing).
Notation rexpr_select_word_sizes_postprocess2 v
  := (renamify v)
       (only parsing).

Local Notation pick_typeb := Bounds.bounds_to_base_type (only parsing).
Local Notation pick_type v := (SmartFlatTypeMap (fun _ => pick_typeb) v).

Notation rexpr_correct_and_boundedT rexprZ rexprW input_bounds output_bounds
  := (let t := _ in
      let e : Expr t := rexprZ in
      let input_bounds : interp_flat_type Bounds.interp_base_type (domain t)
          := input_bounds in
      let output_bounds : interp_flat_type Bounds.interp_base_type (codomain t)
          := output_bounds in
      forall (v : interp_flat_type Syntax.interp_base_type (domain t))
             (v' : interp_flat_type Syntax.interp_base_type (pick_type input_bounds)),
         (Bounds.is_bounded_by input_bounds v /\ cast_back_flat_const v' = v)
         -> Bounds.is_bounded_by output_bounds (Interp interp_op e v)
            /\ cast_back_flat_const (Interp interp_op rexprW v') = Interp interp_op e v)
       (only parsing).

Notation rexpr_correct_and_bounded rexprZ rexprW input_bounds output_bounds rexprZ_Wf
  := (fun v v' Hv
      => proj2
           (@MapBoundsPackagedCorrect
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
  let rexprW_pkgo := (eval vm_compute in (rexpr_select_word_sizes_option rexprZ bounds)) in
  let rexprW_pkg := (eval vm_compute in (rexpr_select_word_sizes_postprocess1 rexprW_pkgo)) in
  let rexprT := constr:(get_output_type rexprW_pkg) in
  let rexprW' := (eval vm_compute in (get_output_expr rexprW_pkg)) in
  let rexprW := (eval cbv beta iota zeta in (rexpr_select_word_sizes_postprocess2 rexprW')) in
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
Ltac specialize_Hcorrectness Hcorrectness :=
  lazymatch goal with
  | [ |- @Bounds.is_bounded_by (codomain ?T) ?bounds (Interp _ ?fZ ?v')
         /\ cast_back_flat_const ?fW = Interp _ ?fZ ?v' ]
    => let v := lazymatch v' with cast_back_flat_const ?v => v end in
       specialize (Hcorrectness v' v);
       lazymatch type of Hcorrectness with
       | ?T -> Bounds.is_bounded_by _ _ /\ cast_back_flat_const ?fW' = _
         => let fWev := (eval cbv delta [fW] in fW) in
            unify fWev fW'; cut T
       end;
       [ let H := fresh in intro H; specialize (Hcorrectness H) | ]
  end.
Ltac handle_bounds_from_hyps :=
  repeat match goal with
         | _ => assumption
         | [ |- cast_back_flat_const _ = cast_back_flat_const _ ] => reflexivity
         | [ |- _ /\ _ ] => split
         | [ |- Bounds.is_bounded_by (_, _) _ ] => split
         end.
Ltac do_pre_wf_pipeline :=
  lazymatch goal with
  | [ |- @Bounds.is_bounded_by (codomain ?T) ?bounds (Interp _ ?fZ ?v')
         /\ cast_back_flat_const ?fW = Interp _ ?fZ ?v' ]
    => rewrite <- !(InterpPreWfPipeline fZ);
       let fZ' := fresh fZ in
       rename fZ into fZ';
       set (fZ := PreWfPipeline fZ');
       vm_compute in fZ; clear fZ'
  end.
assert_reflective.
Time all: [ > reify_sig | cbv beta iota in * | .. ].
do_pre_wf_pipeline.
Time assert_wf.
do_pose_correctness Hcorrectness.
tighten_bounds_from_correctness Hcorrectness.
specialize_Hcorrectness Hcorrectness.
Time exact Hcorrectness.
Time handle_bounds_from_hyps.
  Time Defined.

End BoundedField25p5.
