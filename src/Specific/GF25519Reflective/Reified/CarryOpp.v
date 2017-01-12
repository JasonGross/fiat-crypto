Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rcarry_oppZ_sig : rexpr_unop_sig carry_opp. Proof. reify_sig. Defined.
Definition rcarry_oppZ := Eval vm_compute in proj1_sig rcarry_oppZ_sig.
Lemma rcarry_oppZ_correct_and_bounded_gen : correct_and_bounded_genT rcarry_oppZ rcarry_oppZ_sig.
Proof. rexpr_correct. Qed.
Definition rcarry_opp_output_bounds := Eval vm_compute in compute_bounds rcarry_oppZ ExprUnOp_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition rcarry_oppZ_correct_and_bounded
  := ExprUnOp_correct_and_bounded
       rcarry_oppZ carry_opp rcarry_oppZ_sig rcarry_oppZ_correct_and_bounded_gen
       _ _.

Local Open Scope string_scope.
Compute ("Carry_Opp", compute_bounds_for_display rcarry_oppZ ExprUnOp_bounds).
Compute ("Carry_Opp overflows? ", sanity_compute rcarry_oppZ ExprUnOp_bounds).
Compute ("Carry_Opp overflows (error if it does)? ", sanity_check rcarry_oppZ ExprUnOp_bounds).
