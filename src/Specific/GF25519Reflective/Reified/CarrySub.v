Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rcarry_subZ_sig : rexpr_binop_sig carry_sub. Proof. reify_sig. Defined.
Definition rcarry_subZ := Eval vm_compute in proj1_sig rcarry_subZ_sig.
Lemma rcarry_subZ_correct_and_bounded_gen : correct_and_bounded_genT rcarry_subZ rcarry_subZ_sig.
Proof. rexpr_correct. Qed.
Definition rcarry_sub_output_bounds := Eval vm_compute in compute_bounds rcarry_subZ ExprBinOp_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition rcarry_subZ_correct_and_bounded
  := ExprBinOp_correct_and_bounded
       rcarry_subZ carry_sub rcarry_subZ_sig rcarry_subZ_correct_and_bounded_gen
       _ _.

Local Open Scope string_scope.
Compute ("Carry_Sub", compute_bounds_for_display rcarry_subZ ExprBinOp_bounds).
Compute ("Carry_Sub overflows? ", sanity_compute rcarry_subZ ExprBinOp_bounds).
Compute ("Carry_Sub overflows (error if it does)? ", sanity_check rcarry_subZ ExprBinOp_bounds).
