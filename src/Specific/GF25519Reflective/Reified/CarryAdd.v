Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rcarry_addZ_sig : rexpr_binop_sig carry_add. Proof. reify_sig. Defined.
Definition rcarry_addZ : Expr _ := Eval vm_compute in proj1_sig rcarry_addZ_sig.
Definition rcarry_addW_pkgo := Eval vm_compute in rexpr_select_word_sizes_option rcarry_addZ ExprBinOp_bounds.
Definition rcarry_addW_pkg := Eval vm_compute in rexpr_select_word_sizes_postprocess1 rcarry_addW_pkgo.
Definition rcarry_addT := get_output_type rcarry_addW_pkg.
Definition rcarry_addW' : Expr _ := Eval vm_compute in get_output_expr rcarry_addW_pkg.
Definition rcarry_addW : Expr rcarry_addT := Eval cbv [rcarry_addW'] in rexpr_select_word_sizes_postprocess2 rcarry_addW'.
Definition rcarry_add_output_bounds := Eval vm_compute in get_bounds rcarry_addW_pkg.
Definition rcarry_addZ_Wf : rexpr_wfT rcarry_addZ. Proof. prove_rexpr_wfT. Qed.
Local Obligation Tactic := rexpr_correct_and_bounded_obligation_tac.
Program Definition rcarry_addZ_correct_and_bounded_tight
  : rexpr_correct_and_boundedT rcarry_addZ rcarry_addW ExprBinOp_bounds rcarry_add_output_bounds
  := rexpr_correct_and_bounded rcarry_addZ rcarry_addW ExprBinOp_bounds rcarry_add_output_bounds rcarry_addZ_Wf.

Local Open Scope string_scope.
Compute ("Carry_Add", compute_bounds_for_display rcarry_addW_pkg).
(* We use [compute] rather than [vm_compute] so as to not eta-expand functions, so we get pretty display *)
Eval compute in ("Carry_Add overflows? ", sanity_compute rcarry_addW_pkg).
Compute ("Carry_Add overflows (error if it does)? ", sanity_check rcarry_addW_pkg).
