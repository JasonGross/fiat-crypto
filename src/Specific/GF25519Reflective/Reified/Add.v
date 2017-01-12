Require Import Crypto.Specific.GF25519Reflective.Common.

Definition raddZ_sig : rexpr_binop_sig add. Proof. reify_sig. Defined.
Definition raddZ := Eval vm_compute in proj1_sig raddZ_sig.
Lemma raddZ_correct_and_bounded_gen : correct_and_bounded_genT raddZ raddZ_sig.
Proof. rexpr_correct. Qed.
Definition radd_output_bounds := Eval vm_compute in compute_bounds raddZ ExprBinOp_bounds.

Local Open Scope string_scope.
Compute ("Add", compute_bounds_for_display raddZ ExprBinOp_bounds).
Compute ("Add overflows? ", sanity_compute raddZ ExprBinOp_bounds).
Compute ("Add overflows (error if it does)? ", sanity_check raddZ ExprBinOp_bounds).
