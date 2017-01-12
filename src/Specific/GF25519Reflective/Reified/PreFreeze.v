Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rprefreezeZ_sig : rexpr_unop_sig prefreeze. Proof. reify_sig. Defined.
Definition rprefreezeZ := Eval vm_compute in proj1_sig rprefreezeZ_sig.
Lemma rprefreezeZ_correct_and_bounded_gen : correct_and_bounded_genT rprefreezeZ rprefreezeZ_sig.
Proof. rexpr_correct. Qed.
Definition rprefreeze_output_bounds := Eval vm_compute in compute_bounds rprefreezeZ ExprUnOp_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition rprefreezeZ_correct_and_bounded
  := ExprUnOp_correct_and_bounded
       rprefreezeZ prefreeze rprefreezeZ_sig rprefreezeZ_correct_and_bounded_gen
       _ _.

Local Open Scope string_scope.
Compute ("PreFreeze", compute_bounds_for_display rprefreezeZ ExprUnOp_bounds).
Compute ("PreFreeze overflows? ", sanity_compute rprefreezeZ ExprUnOp_bounds).
Compute ("PreFreeze overflows (error if it does)? ", sanity_check rprefreezeZ ExprUnOp_bounds).
