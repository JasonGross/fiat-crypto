Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rge_modulusZ_sig : rexpr_unop_FEToZ_sig ge_modulus. Proof. reify_sig. Defined.
Definition rge_modulusZ := Eval vm_compute in proj1_sig rge_modulusZ_sig.
Lemma rge_modulusZ_correct_and_bounded_gen : correct_and_bounded_genT rge_modulusZ rge_modulusZ_sig.
Proof. rexpr_correct. Qed.
Definition rge_modulus_output_bounds := Eval vm_compute in compute_bounds rge_modulusZ ExprUnOpFEToZ_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition rge_modulusZ_correct_and_bounded
  := ExprUnOpFEToZ_correct_and_bounded
       rge_modulusZ ge_modulus rge_modulusZ_sig rge_modulusZ_correct_and_bounded_gen
       _ _.

Local Open Scope string_scope.
Compute ("Ge_Modulus", compute_bounds_for_display rge_modulusZ ExprUnOpFEToZ_bounds).
Compute ("Ge_Modulus overflows? ", sanity_compute rge_modulusZ ExprUnOpFEToZ_bounds).
Compute ("Ge_Modulus overflows (error if it does)? ", sanity_check rge_modulusZ ExprUnOpFEToZ_bounds).
