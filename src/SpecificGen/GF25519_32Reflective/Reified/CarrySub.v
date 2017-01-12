Require Import Crypto.SpecificGen.GF25519_32Reflective.Common.

Definition rcarry_subZ_sig : rexpr_binop_sig carry_sub. Proof. reify_sig. Defined.
Definition rcarry_subZ : Syntax.Expr _ _ _ := Eval vm_compute in proj1_sig rcarry_subZ_sig.
Definition rcarry_subW : Syntax.Expr _ _ _ := Eval vm_compute in rexpr_select_word_sizes rcarry_subZ ExprBinOp_bounds.
Definition rcarry_subZ_Wf : rexpr_wfT rcarry_subZ. Proof. prove_rexpr_wfT. Qed.
Definition rcarry_sub_output_bounds
  := Eval vm_compute in compute_bounds rcarry_subZ ExprBinOp_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition rcarry_subZ_correct_and_bounded
  := rexpr_correct_and_bounded rcarry_subZ rcarry_subZ_Wf ExprBinOp_bounds.

Local Open Scope string_scope.
Compute ("Carry_Sub", compute_bounds_for_display rcarry_subZ ExprBinOp_bounds).
Compute ("Carry_Sub overflows? ", sanity_compute rcarry_subZ ExprBinOp_bounds).
Compute ("Carry_Sub overflows (error if it does)? ", sanity_check rcarry_subZ ExprBinOp_bounds).
