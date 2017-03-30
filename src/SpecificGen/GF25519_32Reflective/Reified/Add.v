Require Import Crypto.SpecificGen.GF25519_32Reflective.Common.

Definition raddZ_sig : rexpr_binop_sig add. Proof. reify_sig. Defined.
Definition raddZ : Syntax.Expr _ _ _ := Eval vm_compute in proj1_sig raddZ_sig.
Definition raddW : Syntax.Expr _ _ _ := Eval vm_compute in rexpr_select_word_sizes raddZ ExprBinOp_bounds.
Definition raddZ_Wf : rexpr_wfT raddZ. Proof. prove_rexpr_wfT. Qed.
Definition radd_output_bounds
  := Eval vm_compute in compute_bounds raddZ ExprBinOp_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition raddZ_correct_and_bounded
  := rexpr_correct_and_bounded raddZ raddZ_Wf ExprBinOp_bounds.

Local Open Scope string_scope.
Compute ("Add", compute_bounds_for_display raddZ ExprBinOp_bounds).
Compute ("Add overflows? ", sanity_compute raddZ ExprBinOp_bounds).
Compute ("Add overflows (error if it does)? ", sanity_check raddZ ExprBinOp_bounds).
