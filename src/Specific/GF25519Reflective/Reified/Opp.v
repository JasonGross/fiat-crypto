Require Import Crypto.Specific.GF25519Reflective.Common.

Definition roppZ_sig : rexpr_unop_sig opp. Proof. reify_sig. Defined.
Definition roppZ := Eval vm_compute in proj1_sig roppZ_sig.
Lemma roppZ_correct_and_bounded_gen : correct_and_bounded_genT roppZ roppZ_sig.
Proof. rexpr_correct. Qed.
Definition ropp_output_bounds := Eval vm_compute in compute_bounds roppZ ExprUnOp_bounds.

Local Open Scope string_scope.
Compute ("Opp", compute_bounds_for_display roppZ ExprUnOp_bounds).
Compute ("Opp overflows? ", sanity_compute roppZ ExprUnOp_bounds).
Compute ("Opp overflows (error if it does)? ", sanity_check roppZ ExprUnOp_bounds).
