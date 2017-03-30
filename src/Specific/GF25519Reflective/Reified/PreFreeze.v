Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rprefreezeZ_sig : rexpr_unop_sig prefreeze. Proof. reify_sig. Defined.
Definition rprefreezeZ : Expr _ := Eval vm_compute in proj1_sig rprefreezeZ_sig.
Definition rprefreezeW_pkgo := Eval vm_compute in rexpr_select_word_sizes_option rprefreezeZ ExprUnOp_bounds.
Definition rprefreezeW_pkg := Eval vm_compute in rexpr_select_word_sizes_postprocess1 rprefreezeW_pkgo.
Definition rprefreezeT := get_output_type rprefreezeW_pkg.
Definition rprefreezeW' : Expr _ := Eval vm_compute in get_output_expr rprefreezeW_pkg.
Definition rprefreezeW : Expr rprefreezeT := Eval cbv [rprefreezeW'] in rexpr_select_word_sizes_postprocess2 rprefreezeW'.
Definition rprefreeze_output_bounds := Eval vm_compute in get_bounds rprefreezeW_pkg.
Definition rprefreezeZ_Wf : rexpr_wfT rprefreezeZ. Proof. prove_rexpr_wfT. Qed.
Local Obligation Tactic := rexpr_correct_and_bounded_obligation_tac.
Program Definition rprefreezeZ_correct_and_bounded_tight
  : rexpr_correct_and_boundedT rprefreezeZ rprefreezeW ExprUnOp_bounds rprefreeze_output_bounds
  := rexpr_correct_and_bounded rprefreezeZ rprefreezeW ExprUnOp_bounds rprefreeze_output_bounds rprefreezeZ_Wf.

Local Open Scope string_scope.
Compute ("PreFreeze", compute_bounds_for_display rprefreezeW_pkg).
(* We use [compute] rather than [vm_compute] so as to not eta-expand functions, so we get pretty display *)
Eval compute in ("PreFreeze overflows? ", sanity_compute rprefreezeW_pkg).
Compute ("PreFreeze overflows (error if it does)? ", sanity_check rprefreezeW_pkg).
