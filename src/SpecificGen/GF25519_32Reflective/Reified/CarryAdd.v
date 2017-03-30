Require Import Crypto.SpecificGen.GF25519_32Reflective.Common.

Definition rcarry_addZ_sig : rexpr_binop_sig carry_add. Proof. reify_sig. Defined.
Definition rcarry_addZ : Syntax.Expr _ _ _ := Eval vm_compute in proj1_sig rcarry_addZ_sig.
Definition rcarry_addW : Syntax.Expr _ _ _ := Eval vm_compute in rexpr_select_word_sizes rcarry_addZ ExprBinOp_bounds.
Definition rcarry_addZ_Wf : rexpr_wfT rcarry_addZ. Proof. prove_rexpr_wfT. Qed.
Definition rcarry_add_output_bounds
  := Eval vm_compute in compute_bounds rcarry_addZ ExprBinOp_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition rcarry_addZ_correct_and_bounded
  := rexpr_correct_and_bounded rcarry_addZ rcarry_addZ_Wf ExprBinOp_bounds.

Local Open Scope string_scope.
Compute ("Carry_Add", compute_bounds_for_display rcarry_addZ ExprBinOp_bounds).
Compute ("Carry_Add overflows? ", sanity_compute rcarry_addZ ExprBinOp_bounds).
Compute ("Carry_Add overflows (error if it does)? ", sanity_check rcarry_addZ ExprBinOp_bounds).
