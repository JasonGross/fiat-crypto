Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Algebra.
Require Import Crypto.NewBaseSystem.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Specific.NewBaseSystemTest.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.Tuple Crypto.Util.Notations Crypto.Util.ZRange.
Import ListNotations.

Section Pre.
  Definition BoundedWord n (bitwidth : nat)
             (bounds : tuple zrange n) : Type :=
    { x : tuple (wordT (Nat.log2 bitwidth)) n
    | is_bounded_by None bounds
                    (map wordToZ x)}.

  Definition BoundedWordToZ n w b (BW :BoundedWord n w b)
    : tuple Z n :=  map wordToZ (proj1_sig BW).
End Pre.

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
    | forall a b, phi (add a b) = (phi a + phi b)%F }.
  Proof.
    eexists ?[add]; intros. cbv [phi].
    rewrite <- (proj2_sig add_sig).
    symmetry; rewrite <- (proj2_sig carry_sig); symmetry.
    set (carry_addZ := fun a b => proj1_sig carry_sig (proj1_sig add_sig a b)).
    change (proj1_sig carry_sig (proj1_sig add_sig ?a ?b)) with (carry_addZ a b).
    (* XXX FIXME This is a kludge around anomalies in Coq *)
    Definition recurry1 {T} (F : Z * Z * Z * Z * Z * Z * Z * Z * Z * Z -> T) (x : Z * Z * Z * Z * Z * Z * Z * Z * Z * Z) : T
      := let '(a, b, c, d, e, f, g, h, i, j) := x in
         F ((a, b, c, d, e, f, g, h, i, j)).
    Definition recurry {T} (F : Z * Z * Z * Z * Z * Z * Z * Z * Z * Z * (Z * Z * Z * Z * Z * Z * Z * Z * Z * Z) -> T) (x : Z * Z * Z * Z * Z * Z * Z * Z * Z * Z * (Z * Z * Z * Z * Z * Z * Z * Z * Z * Z)) : T
      := let '(a, b, c, d, e, f, g, h, i, j) := fst x in
         let '(a', b', c', d', e', f', g', h', i', j') := snd x in
         F ((a, b, c, d, e, f, g, h, i, j, (a', b', c', d', e', f', g', h', i', j'))).
    change (proj1_sig carry_sig) with (recurry1 (proj1_sig carry_sig)) in (value of carry_addZ).
    change (proj1_sig add_sig) with (fun x y => recurry (fun xy => proj1_sig add_sig (fst xy) (snd xy)) (x, y)) in (value of carry_addZ).
    cbv beta iota delta [proj1_sig add_sig carry_sig recurry recurry1 runtime_add runtime_and runtime_mul runtime_opp runtime_shr sz] in carry_addZ.
    cbn beta iota delta [fst snd] in carry_addZ.
    apply f_equal.
    (* jgross start here! *)
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

(** The [do_curry] tactic takes a goal of the form
<<
BoundedWordToZ (?f a b ... z) = F A B ... Z
>>
    and turns it into a goal of the form
<<
BoundedWordToZ (f' (a, b, ..., z)) = F' (A, B, ..., Z)
>>
 *)
Ltac do_curry :=
  lazymatch goal with
  | [ |- ?BWtoZ ?f_bw = ?f_Z ]
    => let f_bw := head f_bw in
       let f_Z := head f_Z in
       change_with_curried f_Z;
       let f_bw_name := fresh f_bw in
       set (f_bw_name := f_bw);
       change_with_curried f_bw_name
  end.
(** The [split_BoundedWordToZ] tactic takes a goal of the form
<<
BoundedWordToZ (f args) = F ARGS
>>
    and splits it into a conjunction, one part about the computational
    behavior, and another part about the boundedness.  *)
Ltac count_tuple_length T :=
  lazymatch T with
  | (?A * ?B)%type => let a := count_tuple_length A in
                      let b := count_tuple_length B in
                      (eval compute in (a + b)%nat)
  | _ => constr:(1%nat)
  end.
Ltac make_evar_for_first_projection :=
  lazymatch goal with
  | [ |- @map ?N1 ?A ?B wordToZ (@proj1_sig _ ?P (?f ?args)) = _ ]
    => let T := type of args in
       let N := count_tuple_length T in
       let map' := (eval compute in (@map N)) in
       let proj1_sig' := (eval compute in @proj1_sig) in
       let pf := fresh in
       let y := fresh in
       refine (let y := @map N1 A B wordToZ (_ (map' _ _ (proj1_sig' _ _) args)) in _);
       simple refine (let pf := _ in _);
       [ shelve
       | subst y f
       | etransitivity_rev y;
         subst y;
         clearbody pf;
         cbv beta iota;
         [ lazymatch goal with
           | [ |- ?map ?wordToZ (?f ?args) = ?RHS ]
             => cut (P (f args) /\ map wordToZ (f args) = RHS); [ refine (@proj2 _ _) | exact pf ]
           end
         | subst f; cbn [fst snd]; apply f_equal;
           instantiate (2:=ltac:(repeat intros [? ?]; refine (exist _ _ _)))(* XXX FIXME: Is 2 always the right number? *) ] ];
       cbn [proj1_sig]
  end.
Ltac split_BoundedWordToZ :=
  repeat match goal with
         | [ |- context[BoundedWordToZ _ _ _ ?x] ]
           => is_var x; destruct x
         end;
  unfold BoundedWordToZ; cbn [proj1_sig];
  make_evar_for_first_projection.
(** The [zrange_to_reflective] tactic takes a goal of the form
<<
is_bounded_by _ bounds (map wordToZ (?fW args)) /\ map wordToZ (?fW args) = fZ argsZ
>>
    and uses [cut] and a small lemma to turn it into a goal that the
    reflective machinery can handle.  The goal left by this tactic
    should be fully solvable by the reflective pipeline. *)

Ltac const_tuple T val :=
  lazymatch T with
  | (?A * ?B)%type => let a := const_tuple A val in
                      let b := const_tuple B val in
                      constr:((a, b)%core)
  | _ => val
  end.
Lemma adjust_goal_for_reflective {T P} (LHS RHS : T)
  : P RHS /\ LHS = RHS -> P LHS /\ LHS = RHS.
Proof. intros [? ?]; subst; tauto. Qed.
Ltac adjust_goal_for_reflective := apply adjust_goal_for_reflective.
Ltac zrange_to_reflective :=
  lazymatch goal with
  | [ |- @ZRange.is_bounded_by ?option_bit_width ?count ?bounds (Tuple.map wordToZ (?reified_f_evar ?args))
         /\ Tuple.map wordToZ (?reified_f_evar ?args) = ?f ?Zargs ]
    => let T := type of f in
       let f_domain := lazymatch T with ?A -> ?B => A end in
       let T := (eval compute in T) in
       let rT := reify_type T in
       let is_bounded_by' := constr:(@Bounds.is_bounded_by (codomain rT)) in
       let input_bounds := const_tuple f_domain bounds in
       let map_t := constr:(fun t bs => @cast_back_flat_const (@Bounds.interp_base_type) t (fun _ => Bounds.bounds_to_base_type) bs) in
       let map_output := constr:(map_t (codomain rT) bounds) in
       let map_input := constr:(map_t (domain rT) input_bounds) in
       (* we use [cut] and [abstract] rather than [change] to catch inefficiencies in conversion early, rather than allowing [Defined] to take forever *)
       cut (is_bounded_by' bounds (map_output (reified_f_evar args)) /\ map_output (reified_f_evar args) = f (map_input args));
       [ generalize reified_f_evar; clear; clearbody f; let x := fresh in intros ? x; abstract exact x
       | ];
       cbv beta
  end;
  adjust_goal_for_reflective.
Require Import Crypto.Reflection.Z.Bounds.Relax.
do_curry.
split_BoundedWordToZ.
zrange_to_reflective.


Require Import Crypto.Reflection.Z.MapBounds.
Require Import Crypto.Reflection.Z.MapBoundsInterp.
Require Import Crypto.Reflection.RenameBinders.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Util.Option.
Require Import Crypto.Reflection.WfReflective.
Require Import Crypto.Reflection.SmartMap.

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
         /\ cast_back_flat_const (?fW ?v) = ?fZ (cast_back_flat_const ?v) ]
    => let rexpr := fresh "rexpr" in
       simple refine (let rexpr : { rexpr | forall x, Interp interp_op (t:=T) rexpr x = fZ x } := _ in _);
         [
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
         /\ cast_back_flat_const (?fW ?v) = Interp _ ?fZ (@cast_back_flat_const _ _ _ ?input_bounds ?v) ]
    => assert (Wf fZ) by prove_rexpr_wfT
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
  intros;
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
         /\ cast_back_flat_const (?fW ?v) = Interp _ ?fZ (@cast_back_flat_const _ _ _ ?input_bounds ?v) ]
    => make_correctness fZ input_bounds Hcorrectness
  end.
Ltac pretighten_bounds tighter_bounds :=
  lazymatch goal with
  | [ |- @Bounds.is_bounded_by ?t ?relaxed_bounds _ /\ cast_back_flat_const ?v = ?k ]
    => simple refine (@relax_output_bounds t tighter_bounds relaxed_bounds _ v k _ _)
  end.
Ltac posttighten_bounds :=
  [ > clear; vm_compute; reflexivity | unfold eq_rect | clear ].
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
         /\ cast_back_flat_const (?fW ?v) = Interp _ ?fZ ?v' ]
    => specialize (Hcorrectness v' v);
       lazymatch type of Hcorrectness with
       | ?T -> Bounds.is_bounded_by _ _ /\ cast_back_flat_const (?fW' _) = _
         => unify fW fW'; cut T
       end;
       [ let H := fresh in intro H; specialize (Hcorrectness H) | ]
  end.
assert_reflective.
cbv [interp_flat_type interp_base_type Tuple.tuple Tuple.tuple'] in *.
reify_sig.
cbv beta iota in *.
assert_wf.
do_pose_correctness Hcorrectness.
tighten_bounds_from_correctness Hcorrectness.
specialize_Hcorrectness Hcorrectness.
exact Hcorrectness.
Ltac handle_bounds_from_hyps :=
  repeat match goal with
         | _ => assumption
         | [ |- cast_back_flat_const _ = cast_back_flat_const _ ] => reflexivity
         | [ |- _ /\ _ ] => split
         | [ |- Bounds.is_bounded_by (_, _) _ ] => split
         end.
{ handle_bounds_from_hyps. }
2:reflexivity.
  Admitted.

End BoundedField25p5.
