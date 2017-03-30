Require Import Crypto.SpecificGen.GF25519_64Reflective.Common.

Definition rcarry_oppZ_sig : rexpr_unop_sig carry_opp. Proof. reify_sig. Defined.
Definition rcarry_oppZ : Syntax.Expr _ _ _ := Eval vm_compute in proj1_sig rcarry_oppZ_sig.
Definition rcarry_oppW : Syntax.Expr _ _ _ := Eval vm_compute in rexpr_select_word_sizes rcarry_oppZ ExprUnOp_bounds.
Definition rcarry_oppZ_Wf : rexpr_wfT rcarry_oppZ. Proof. prove_rexpr_wfT. Qed.
Definition rcarry_opp_output_bounds
  := Eval vm_compute in compute_bounds rcarry_oppZ ExprUnOp_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition rcarry_oppZ_correct_and_bounded
  := rexpr_correct_and_bounded rcarry_oppZ rcarry_oppZ_Wf ExprUnOp_bounds.

Local Open Scope string_scope.
Compute ("Carry_Opp", compute_bounds_for_display rcarry_oppZ ExprUnOp_bounds).
Compute ("Carry_Opp overflows? ", sanity_compute rcarry_oppZ ExprUnOp_bounds).
Compute ("Carry_Opp overflows (error if it does)? ", sanity_check rcarry_oppZ ExprUnOp_bounds).
