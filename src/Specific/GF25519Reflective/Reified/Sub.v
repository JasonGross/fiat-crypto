Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rsubZ_sig : rexpr_binop_sig sub. Proof. reify_sig. Defined.
Definition rsubZ := Eval vm_compute in proj1_sig rsubZ_sig.
Lemma rsubZ_correct_and_bounded_gen : correct_and_bounded_genT rsubZ rsubZ_sig.
Proof. rexpr_correct. Qed.
Definition rsub_output_bounds := Eval vm_compute in compute_bounds rsubZ ExprBinOp_bounds.

Local Open Scope string_scope.
Compute ("Sub", compute_bounds_for_display rsubZ ExprBinOp_bounds).
Compute ("Sub overflows? ", sanity_compute rsubZ ExprBinOp_bounds).
Compute ("Sub overflows (error if it does)? ", sanity_check rsubZ ExprBinOp_bounds).
