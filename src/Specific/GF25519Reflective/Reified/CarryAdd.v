Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rcarry_addZ_sig : rexpr_binop_sig carry_add. Proof. reify_sig. Defined.
Definition rcarry_addZ := Eval vm_compute in proj1_sig rcarry_addZ_sig.
Lemma rcarry_addZ_correct_and_bounded_gen : correct_and_bounded_genT rcarry_addZ rcarry_addZ_sig.
Proof. rexpr_correct. Qed.
Definition rcarry_add_output_bounds := Eval vm_compute in compute_bounds rcarry_addZ ExprBinOp_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition rcarry_addZ_correct_and_bounded
  := ExprBinOp_correct_and_bounded
       rcarry_addZ carry_add rcarry_addZ_sig rcarry_addZ_correct_and_bounded_gen
       _ _.

Local Open Scope string_scope.
Compute ("Carry_Add", compute_bounds_for_display rcarry_addZ ExprBinOp_bounds).
Compute ("Carry_Add overflows? ", sanity_compute rcarry_addZ ExprBinOp_bounds).
Compute ("Carry_Add overflows (error if it does)? ", sanity_check rcarry_addZ ExprBinOp_bounds).
