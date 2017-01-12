Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rpackZ_sig : rexpr_unop_FEToWire_sig pack. Proof. reify_sig. Defined.
Definition rpackZ := Eval vm_compute in proj1_sig rpackZ_sig.
Lemma rpackZ_correct_and_bounded_gen : correct_and_bounded_genT rpackZ rpackZ_sig.
Proof. rexpr_correct. Qed.
Definition rpack_output_bounds := Eval vm_compute in compute_bounds rpackZ ExprUnOpFEToWire_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition rpackZ_correct_and_bounded
  := ExprUnOpFEToWire_correct_and_bounded
       rpackZ pack rpackZ_sig rpackZ_correct_and_bounded_gen
       _ _.

Local Open Scope string_scope.
Compute ("Pack", compute_bounds_for_display rpackZ ExprUnOpFEToWire_bounds).
Compute ("Pack overflows? ", sanity_compute rpackZ ExprUnOpFEToWire_bounds).
Compute ("Pack overflows (error if it does)? ", sanity_check rpackZ ExprUnOpFEToWire_bounds).
