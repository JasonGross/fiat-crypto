Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rmulZ_sig : rexpr_binop_sig mul. Proof. reify_sig. Defined.
Definition rmulZ := Eval vm_compute in proj1_sig rmulZ_sig.
Lemma rmulZ_correct_and_bounded_gen : correct_and_bounded_genT rmulZ rmulZ_sig.
Proof. rexpr_correct. Qed.
Definition rmul_output_bounds := Eval vm_compute in compute_bounds rmulZ ExprBinOp_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition rmulZ_correct_and_bounded
  := ExprBinOp_correct_and_bounded
       rmulZ mul rmulZ_sig rmulZ_correct_and_bounded_gen
       _ _.

Local Open Scope string_scope.
Compute ("Mul", compute_bounds_for_display rmulZ ExprBinOp_bounds).
Compute ("Mul overflows? ", sanity_compute rmulZ ExprBinOp_bounds).
Compute ("Mul overflows (error if it does)? ", sanity_check rmulZ ExprBinOp_bounds).
