Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rcarry_oppZ_sig : rexpr_unop_sig carry_opp. Proof. reify_sig. Defined.
Definition rcarry_oppZ : Expr _ := Eval vm_compute in proj1_sig rcarry_oppZ_sig.
Definition rcarry_oppW_pkgo := Eval vm_compute in rexpr_select_word_sizes_option rcarry_oppZ ExprUnOp_bounds.
Definition rcarry_oppW_pkg := Eval vm_compute in rexpr_select_word_sizes_postprocess1 rcarry_oppW_pkgo.
Definition rcarry_oppT := get_output_type rcarry_oppW_pkg.
Definition rcarry_oppW' : Expr _ := Eval vm_compute in get_output_expr rcarry_oppW_pkg.
Definition rcarry_oppW : Expr rcarry_oppT := Eval cbv [rcarry_oppW'] in rexpr_select_word_sizes_postprocess2 rcarry_oppW'.
Definition rcarry_opp_output_bounds := Eval vm_compute in get_bounds rcarry_oppW_pkg.
Definition rcarry_oppZ_Wf : rexpr_wfT rcarry_oppZ. Proof. prove_rexpr_wfT. Qed.
Local Obligation Tactic := rexpr_correct_and_bounded_obligation_tac.
Program Definition rcarry_oppZ_correct_and_bounded_tight
  : rexpr_correct_and_boundedT rcarry_oppZ rcarry_oppW ExprUnOp_bounds rcarry_opp_output_bounds
  := rexpr_correct_and_bounded rcarry_oppZ rcarry_oppW ExprUnOp_bounds rcarry_opp_output_bounds rcarry_oppZ_Wf.

Local Open Scope string_scope.
Compute ("Carry_Opp", compute_bounds_for_display rcarry_oppW_pkg).
(* We use [compute] rather than [vm_compute] so as to not eta-expand functions, so we get pretty display *)
Eval compute in ("Carry_Opp overflows? ", sanity_compute rcarry_oppW_pkg).
Compute ("Carry_Opp overflows (error if it does)? ", sanity_check rcarry_oppW_pkg).
