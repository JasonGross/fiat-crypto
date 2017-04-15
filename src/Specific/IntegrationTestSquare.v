Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Specific.ArithmeticSynthesisTest.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.Tuple Crypto.Util.Sigma Crypto.Util.Sigma.MapProjections Crypto.Util.Sigma.Lift Crypto.Util.Notations Crypto.Util.ZRange Crypto.Util.BoundedWord.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.MoveLetIn.
Import ListNotations.

Require Import Crypto.Specific.IntegrationTestTemporaryMiscCommon.

Require Import Crypto.Compilers.Z.Bounds.Pipeline.

Section BoundedField25p5.
  Local Coercion Z.of_nat : nat >-> Z.

  Let limb_widths := Eval vm_compute in (List.map (fun i => Z.log2 (wt (S i) / wt i)) (seq 0 sz)).
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

  Let lgbitwidth := Eval compute in (Z.to_nat (Z.log2_up (List.fold_right Z.max 0 limb_widths))).
  Let bitwidth := Eval compute in (2^lgbitwidth)%nat.
  Let feZ : Type := tuple Z sz.
  Let feW : Type := tuple (wordT lgbitwidth) sz.
  Let feBW : Type := BoundedWord sz bitwidth bounds.
  Let phi : feBW -> F m :=
    fun x => B.Positional.Fdecode wt (BoundedWordToZ _ _ _ x).

  (* TODO : change this to field once field isomorphism happens *)
  Definition square :
    { square : feBW -> feBW
    | forall a, phi (square a) = F.mul (phi a) (phi a) }.
  Proof.
    lazymatch goal with
    | [ |- { f | forall a, ?phi (f a) = @?rhs a } ]
      => apply lift1_sig with (P:=fun a f => phi f = rhs a)
    end.
    intros.
    eexists_sig_etransitivity. all:cbv [phi].
    rewrite <- (proj2_sig mul_sig).
    symmetry; rewrite <- (proj2_sig carry_sig); symmetry.
    set (carry_squareZ := fun a => proj1_sig carry_sig (proj1_sig mul_sig a a)).
    change (proj1_sig carry_sig (proj1_sig mul_sig ?a ?a)) with (carry_squareZ a).
    context_to_dlet_in_rhs carry_squareZ.
    cbv beta iota delta [carry_squareZ proj1_sig mul_sig carry_sig fst snd runtime_add runtime_and runtime_mul runtime_opp runtime_shr sz].
    reflexivity.
    sig_dlet_in_rhs_to_context.
    apply (fun f => proj2_sig_map (fun THIS_NAME_MUST_NOT_BE_UNDERSCORE_TO_WORK_AROUND_CONSTR_MATCHING_ANAOMLIES___BUT_NOTE_THAT_IF_THIS_NAME_IS_LOWERCASE_A___THEN_REIFICATION_STACK_OVERFLOWS___AND_I_HAVE_NO_IDEA_WHATS_GOING_ON p => f_equal f p)).
    (* jgross start here! *)
    (*Set Ltac Profiling.*)
    Time Glue.refine_to_reflective_glue (64::128::nil)%nat%list.
    Time ReflectiveTactics.refine_with_pipeline_correct.
    { Time ReflectiveTactics.do_reify. }
    Require Import CNotations.
    { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { cbv [Pipeline.Definition.PostWfPipeline].
      set (k := Inline.InlineConst _).
      pose (Eta.ExprEta k) as k'.
      vm_compute in k'.
      vm_compute in k.
      assert (var : Syntax.base_type -> Type) by admit.
      refine (let x := _ in
              let y := _ in
              let z := _ in
              let w := _ in
              let v := _ in
              let l := ExprInversion.invert_Abs (Eta.ExprEta (CommonSubexpressionElimination.CSE k') var) (x, y, z, w, v)%core in
              _);
        clearbody x y z w v.
      { exfalso; clear -l.
        cbv [Eta.ExprEta CommonSubexpressionElimination.CSE k' ExprInversion.invert_Abs] in l; clear -l.
        cbv [Eta.expr_eta CommonSubexpressionElimination.CSE_gen] in l.
        cbv [Eta.expr_eta_gen Compilers.CommonSubexpressionElimination.CSE] in l.
        Import Compilers.CommonSubexpressionElimination.
        Import Z.CommonSubexpressionElimination.
        cbv [Eta.interp_flat_type_eta_gen domain codomain interp_flat_type Compilers.CommonSubexpressionElimination.cse ExprInversion.invert_Abs Eta.exprf_eta CommonSubexpressionElimination.prepend_prefix Compilers.CommonSubexpressionElimination.csef CommonSubexpressionElimination.symbolicify_smart_var CommonSubexpressionElimination.symbolize_var CommonSubexpressionElimination.push_pair_symbolic_expr Context.empty SymbolicExprContext AListContext.AListContext SmartMap.SmartVarfMap2 SmartMap.smart_interp_flat_map2] in l; cbn [fst snd length] in l.
        unfold csef_step at 1 in (value of l).
        Notation "( x ; y )" := (existT _ x y).
        Arguments SSnd {_ _ _ _} _.
        Arguments SFst {_ _ _ _} _.

        let k := fresh "k" in set (k := norm_symbolize_exprf (var:=var) Syntax.base_type symbolic_op Syntax.op symbolize_op normalize_symbolic_expr_mod_c _) in (value of l).
        vm_compute in k; subst k.
        unfold csef_step at 1 in (value of l).
        simpl @Context.lookupb in l.
        cbv beta iota in l.
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        cbn [fst snd length] in l.
        unfold csef_step at 1 in (value of l).
        let k := fresh "k" in set (k := norm_symbolize_exprf (var:=var) Syntax.base_type symbolic_op Syntax.op symbolize_op normalize_symbolic_expr_mod_c _) in (value of l).
        vm_compute in k. subst k.
        cbv beta iota in l.
        simpl @Context.lookupb in l.
        cbv beta iota in l.
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        let k := fresh "k" in set (k := norm_symbolize_exprf (var:=var) Syntax.base_type symbolic_op Syntax.op symbolize_op normalize_symbolic_expr_mod_c _) in (value of l).
        vm_compute in k; subst k.
        cbv beta iota in l.
        simpl @Context.lookupb in l.
        cbv beta iota in l.
        cbn [fst snd length] in l.
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        set (k' := @csef_step) in (value of l) at 1.
        cbn [fst snd] in l.
        cbv beta iota delta [csef_step] in k'.
        cbv beta iota delta [k'] in l.
        clear k'.
        let k := fresh "k" in set (k := norm_symbolize_exprf (var:=var) Syntax.base_type symbolic_op Syntax.op symbolize_op normalize_symbolic_expr_mod_c _) in (value of l).
        cbv [norm_symbolize_exprf] in (*** HERE *)
        vm_compute in k.
        let k := fresh "k" in set (k := norm_symbolize_exprf (var:=var) Syntax.base_type symbolic_op Syntax.op symbolize_op normalize_symbolic_expr_mod_c _) in (value of l).
        vm_compute in k; subst k.
        cbv beta iota in l.
        simpl @Context.lookupb in l.
        cbv beta iota in l.
        cbn [fst snd length] in l.
        simpl @Context.extendb in l.
        cbv [AListContext.add] in l.
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        cbv [Eta.interp_flat_type_eta_gen domain codomain interp_flat_type Compilers.CommonSubexpressionElimination.cse ExprInversion.invert_Abs Eta.exprf_eta CommonSubexpressionElimination.prepend_prefix Compilers.CommonSubexpressionElimination.csef CommonSubexpressionElimination.symbolicify_smart_var CommonSubexpressionElimination.symbolize_var CommonSubexpressionElimination.push_pair_symbolic_expr Context.empty SymbolicExprContext AListContext.AListContext SmartMap.SmartVarfMap2 SmartMap.smart_interp_flat_map2 norm_symbolize_exprf symbolize_exprf option_map CommonSubexpressionElimination.symbolize_op Context.extendb AListContext.add] in l; cbn [fst snd length] in l.
        cbv [symbolic_expr_normalize CommonSubexpressionElimination.normalize_symbolic_expr_mod_c CommonSubexpressionElimination.symbolic_op_args_to_list ] in l.
        cbv [CommonSubexpressionElimination.SymbolicExprSort.sort CommonSubexpressionElimination.SymbolicExprSort.iter_merge SymbolicExprSort.merge_list_to_stack SymbolicExprSort.merge_stack SymbolicExprSort.merge] in l.
        cbv [symbolic_op_list_to_args] in l.
        cbv [Eta.interp_flat_type_eta_gen domain codomain interp_flat_type Compilers.CommonSubexpressionElimination.cse ExprInversion.invert_Abs Eta.exprf_eta CommonSubexpressionElimination.prepend_prefix Compilers.CommonSubexpressionElimination.csef CommonSubexpressionElimination.symbolicify_smart_var CommonSubexpressionElimination.symbolize_var CommonSubexpressionElimination.push_pair_symbolic_expr Context.empty SymbolicExprContext AListContext.AListContext SmartMap.SmartVarfMap2 SmartMap.smart_interp_flat_map2 norm_symbolize_exprf symbolize_exprf option_map CommonSubexpressionElimination.symbolize_op Context.extendb AListContext.add Context.lookupb AListContext.find symbolic_expr_beq] in l; cbn [fst snd length] in l.
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        cbn [fst snd] in l.
        unfold csef_step at 1 in (value of l).
        cbv [norm_symbolize_exprf option_map symbolize_exprf symbolic_expr_normalize CommonSubexpressionElimination.normalize_symbolic_expr_mod_c CommonSubexpressionElimination.symbolic_op_args_to_list ] in l.
        cbv [Eta.interp_flat_type_eta_gen domain codomain interp_flat_type Compilers.CommonSubexpressionElimination.cse ExprInversion.invert_Abs Eta.exprf_eta CommonSubexpressionElimination.prepend_prefix Compilers.CommonSubexpressionElimination.csef CommonSubexpressionElimination.symbolicify_smart_var CommonSubexpressionElimination.symbolize_var CommonSubexpressionElimination.push_pair_symbolic_expr Context.empty SymbolicExprContext AListContext.AListContext SmartMap.SmartVarfMap2 SmartMap.smart_interp_flat_map2 norm_symbolize_exprf symbolize_exprf option_map CommonSubexpressionElimination.symbolize_op Context.extendb AListContext.add Context.lookupb AListContext.find symbolic_expr_beq flat_type_beq symbolic_op_beq Syntax.base_type_beq andb] in l; cbn [fst snd length] in l.
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        cbn [fst snd] in l.
        cbv [norm_symbolize_exprf option_map symbolize_exprf symbolic_expr_normalize CommonSubexpressionElimination.normalize_symbolic_expr_mod_c CommonSubexpressionElimination.symbolic_op_args_to_list ] in l.
        cbv [Eta.interp_flat_type_eta_gen domain codomain interp_flat_type Compilers.CommonSubexpressionElimination.cse ExprInversion.invert_Abs Eta.exprf_eta CommonSubexpressionElimination.prepend_prefix Compilers.CommonSubexpressionElimination.csef CommonSubexpressionElimination.symbolicify_smart_var CommonSubexpressionElimination.symbolize_var CommonSubexpressionElimination.push_pair_symbolic_expr Context.empty SymbolicExprContext AListContext.AListContext SmartMap.SmartVarfMap2 SmartMap.smart_interp_flat_map2 norm_symbolize_exprf symbolize_exprf option_map CommonSubexpressionElimination.symbolize_op Context.extendb AListContext.add Context.lookupb AListContext.find symbolic_expr_beq flat_type_beq symbolic_op_beq Syntax.base_type_beq andb] in l; cbn [fst snd length] in l.
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        cbn [fst snd] in l.
        cbv [norm_symbolize_exprf option_map symbolize_exprf symbolic_expr_normalize CommonSubexpressionElimination.normalize_symbolic_expr_mod_c CommonSubexpressionElimination.symbolic_op_args_to_list ] in l.
        cbv [Eta.interp_flat_type_eta_gen domain codomain interp_flat_type Compilers.CommonSubexpressionElimination.cse ExprInversion.invert_Abs Eta.exprf_eta CommonSubexpressionElimination.prepend_prefix Compilers.CommonSubexpressionElimination.csef CommonSubexpressionElimination.symbolicify_smart_var CommonSubexpressionElimination.symbolize_var CommonSubexpressionElimination.push_pair_symbolic_expr Context.empty SymbolicExprContext AListContext.AListContext SmartMap.SmartVarfMap2 SmartMap.smart_interp_flat_map2 norm_symbolize_exprf symbolize_exprf option_map CommonSubexpressionElimination.symbolize_op Context.extendb AListContext.add Context.lookupb AListContext.find symbolic_expr_beq flat_type_beq symbolic_op_beq Syntax.base_type_beq andb] in l; cbn [fst snd length] in l.
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        unfold csef_step at 1 in (value of l).
        cbv [Context.lookupb] in l.
        set
      set (l := CommonSubexpressionElimination.CSE _).
      set (l' := Eta.ExprEta l).
      cbv [CommonSubexpressionElimination.CSE k]
      Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_rhs_reflexivity. }
    { Time ReflectiveTactics.unify_abstract_renamify_rhs_reflexivity. }
    { Time SubstLet.subst_let; clear; abstract vm_cast_no_check (eq_refl true). }
    { Time SubstLet.subst_let; clear; vm_compute; reflexivity. }
    { Time UnifyAbstractReflexivity.unify_abstract_compute_rhs_reflexivity. }
    { Time ReflectiveTactics.unify_abstract_cbv_interp_rhs_reflexivity. }
    { Time abstract ReflectiveTactics.handle_bounds_from_hyps. }

    Time refine_reflectively. (* Finished transaction in 19.348 secs (19.284u,0.036s) (successful) *)
    (*Show Ltac Profile.*)
    (* total time:     19.632s

 tactic                                   local  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─refine_reflectively -------------------   0.0%  98.4%       1   19.320s
─ReflectiveTactics.do_reflective_pipelin  -0.0%  96.2%       1   18.884s
─ReflectiveTactics.solve_side_conditions   1.2%  96.1%       1   18.860s
─ReflectiveTactics.do_reify ------------  27.7%  44.0%       1    8.640s
─ReflectiveTactics.abstract_vm_compute_r  12.3%  13.9%       2    2.024s
─ReflectiveTactics.abstract_vm_compute_r   8.9%  12.2%       2    1.576s
─Reify_rhs_gen -------------------------   0.8%  11.7%       1    2.300s
─ReflectiveTactics.renamify_rhs --------  10.4%  11.5%       1    2.260s
─ReflectiveTactics.abstract_rhs --------   4.6%   5.8%       1    1.148s
─clear (var_list) ----------------------   5.2%   5.2%      57    0.184s
─eexact --------------------------------   4.1%   4.1%      68    0.028s
─prove_interp_compile_correct ----------   0.0%   3.4%       1    0.664s
─ReflectiveTactics.abstract_cbv_interp_r   2.7%   3.3%       1    0.648s
─unify (constr) (constr) ---------------   3.2%   3.2%       6    0.248s
─rewrite ?EtaInterp.InterpExprEta ------   3.1%   3.1%       1    0.612s
─ReflectiveTactics.abstract_cbv_rhs ----   2.0%   2.7%       1    0.532s
─Glue.refine_to_reflective_glue --------   0.0%   2.2%       1    0.436s
─rewrite H -----------------------------   2.1%   2.1%       1    0.420s

 tactic                                   local  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─refine_reflectively -------------------   0.0%  98.4%       1   19.320s
 ├─ReflectiveTactics.do_reflective_pipel  -0.0%  96.2%       1   18.884s
 │└ReflectiveTactics.solve_side_conditio   1.2%  96.1%       1   18.860s
 │ ├─ReflectiveTactics.do_reify --------  27.7%  44.0%       1    8.640s
 │ │ ├─Reify_rhs_gen -------------------   0.8%  11.7%       1    2.300s
 │ │ │ ├─prove_interp_compile_correct --   0.0%   3.4%       1    0.664s
 │ │ │ │└rewrite ?EtaInterp.InterpExprEt   3.1%   3.1%       1    0.612s
 │ │ │ └─rewrite H ---------------------   2.1%   2.1%       1    0.420s
 │ │ └─eexact --------------------------   4.1%   4.1%      68    0.028s
 │ ├─ReflectiveTactics.abstract_vm_compu  12.3%  13.9%       2    2.024s
 │ ├─ReflectiveTactics.abstract_vm_compu   8.9%  12.2%       2    1.576s
 │ ├─ReflectiveTactics.renamify_rhs ----  10.4%  11.5%       1    2.260s
 │ ├─ReflectiveTactics.abstract_rhs ----   4.6%   5.8%       1    1.148s
 │ ├─ReflectiveTactics.abstract_cbv_inte   2.7%   3.3%       1    0.648s
 │ └─ReflectiveTactics.abstract_cbv_rhs    2.0%   2.7%       1    0.532s
 └─Glue.refine_to_reflective_glue ------   0.0%   2.2%       1    0.436s
*)
  Time Defined. (* Finished transaction in 10.167 secs (10.123u,0.023s) (successful) *)

End BoundedField25p5.
