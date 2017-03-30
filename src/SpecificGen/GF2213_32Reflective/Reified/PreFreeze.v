Require Import Crypto.SpecificGen.GF2213_32Reflective.Common.

Definition rprefreezeZ_sig : rexpr_unop_sig prefreeze. Proof. reify_sig. Defined.
Definition rprefreezeZ : Syntax.Expr _ _ _ := Eval vm_compute in proj1_sig rprefreezeZ_sig.
Definition rprefreezeW : Syntax.Expr _ _ _ := Eval vm_compute in rexpr_select_word_sizes rprefreezeZ ExprUnOp_bounds.
Definition rprefreezeZ_Wf : rexpr_wfT rprefreezeZ. Proof. prove_rexpr_wfT. Qed.
Definition rprefreeze_output_bounds
  := Eval vm_compute in compute_bounds rprefreezeZ ExprUnOp_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition rprefreezeZ_correct_and_bounded
  := rexpr_correct_and_bounded rprefreezeZ rprefreezeZ_Wf ExprUnOp_bounds.

Local Open Scope string_scope.
Compute ("PreFreeze", compute_bounds_for_display rprefreezeZ ExprUnOp_bounds).
Compute ("PreFreeze overflows? ", sanity_compute rprefreezeZ ExprUnOp_bounds).
Compute ("PreFreeze overflows (error if it does)? ", sanity_check rprefreezeZ ExprUnOp_bounds).
