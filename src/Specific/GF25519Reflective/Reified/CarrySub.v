Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rcarry_subZ_sig : rexpr_binop_sig carry_sub. Proof. reify_sig. Defined.
Definition rcarry_subZ : Expr _ := Eval vm_compute in proj1_sig rcarry_subZ_sig.
Definition rcarry_subW_pkgo := Eval vm_compute in rexpr_select_word_sizes_option rcarry_subZ ExprBinOp_bounds.
Definition rcarry_subW_pkg := Eval vm_compute in rexpr_select_word_sizes_postprocess1 rcarry_subW_pkgo.
Definition rcarry_subT := get_output_type rcarry_subW_pkg.
Definition rcarry_subW' : Expr _ := Eval vm_compute in get_output_expr rcarry_subW_pkg.
Definition rcarry_subW : Expr rcarry_subT := Eval cbv [rcarry_subW'] in rexpr_select_word_sizes_postprocess2 rcarry_subW'.
Definition rcarry_sub_output_bounds := Eval vm_compute in get_bounds rcarry_subW_pkg.
Definition rcarry_subZ_Wf : rexpr_wfT rcarry_subZ. Proof. prove_rexpr_wfT. Qed.
Local Obligation Tactic := rexpr_correct_and_bounded_obligation_tac.
Program Definition rcarry_subZ_correct_and_bounded_tight
  : rexpr_correct_and_boundedT rcarry_subZ rcarry_subW ExprBinOp_bounds rcarry_sub_output_bounds
  := rexpr_correct_and_bounded rcarry_subZ rcarry_subW ExprBinOp_bounds rcarry_sub_output_bounds rcarry_subZ_Wf.

Local Open Scope string_scope.
Compute ("Carry_Sub", compute_bounds_for_display rcarry_subW_pkg).
(* We use [compute] rather than [vm_compute] so as to not eta-expand functions, so we get pretty display *)
Eval compute in ("Carry_Sub overflows? ", sanity_compute rcarry_subW_pkg).
Compute ("Carry_Sub overflows (error if it does)? ", sanity_check rcarry_subW_pkg).
