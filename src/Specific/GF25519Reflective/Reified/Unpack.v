Require Import Crypto.Specific.GF25519Reflective.Common.

Definition runpackZ_sig : rexpr_unop_WireToFE_sig unpack. Proof. reify_sig. Defined.
Definition runpackZ := Eval vm_compute in proj1_sig runpackZ_sig.
Lemma runpackZ_correct_and_bounded_gen : correct_and_bounded_genT runpackZ runpackZ_sig.
Proof. rexpr_correct. Qed.
Definition runpack_output_bounds := Eval vm_compute in compute_bounds runpackZ ExprUnOpWireToFE_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition runpackZ_correct_and_bounded
  := ExprUnOpWireToFE_correct_and_bounded
       runpackZ unpack runpackZ_sig runpackZ_correct_and_bounded_gen
       _ _.

Local Open Scope string_scope.
Compute ("Unpack", compute_bounds_for_display runpackZ ExprUnOpWireToFE_bounds).
Compute ("Unpack overflows? ", sanity_compute runpackZ ExprUnOpWireToFE_bounds).
Compute ("Unpack overflows (error if it does)? ", sanity_check runpackZ ExprUnOpWireToFE_bounds).
