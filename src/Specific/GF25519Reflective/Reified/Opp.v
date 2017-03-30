Require Import Crypto.Specific.GF25519Reflective.Common.

Definition roppZ_sig : rexpr_unop_sig opp. Proof. reify_sig. Defined.
Definition roppZ : Expr _ := Eval vm_compute in proj1_sig roppZ_sig.
Definition roppW_pkgo := Eval vm_compute in rexpr_select_word_sizes_option roppZ ExprUnOp_bounds.
Definition roppW_pkg := Eval vm_compute in rexpr_select_word_sizes_postprocess1 roppW_pkgo.
Definition roppT := get_output_type roppW_pkg.
Definition roppW' : Expr _ := Eval vm_compute in get_output_expr roppW_pkg.
Definition roppW : Expr roppT := Eval cbv [roppW'] in rexpr_select_word_sizes_postprocess2 roppW'.
Definition ropp_output_bounds := Eval vm_compute in get_bounds roppW_pkg.
Definition roppZ_Wf : rexpr_wfT roppZ. Proof. prove_rexpr_wfT. Qed.
Local Obligation Tactic := rexpr_correct_and_bounded_obligation_tac.
Program Definition roppZ_correct_and_bounded_tight
  : rexpr_correct_and_boundedT roppZ roppW ExprUnOp_bounds ropp_output_bounds
  := rexpr_correct_and_bounded roppZ roppW ExprUnOp_bounds ropp_output_bounds roppZ_Wf.

Local Open Scope string_scope.
Compute ("Opp", compute_bounds_for_display roppW_pkg).
(* We use [compute] rather than [vm_compute] so as to not eta-expand functions, so we get pretty display *)
Eval compute in ("Opp overflows? ", sanity_compute roppW_pkg).
Compute ("Opp overflows (error if it does)? ", sanity_check roppW_pkg).
