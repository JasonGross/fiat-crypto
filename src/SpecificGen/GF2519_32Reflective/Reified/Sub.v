Require Import Crypto.SpecificGen.GF2519_32Reflective.Common.

Definition rsubZ_sig : rexpr_binop_sig sub. Proof. reify_sig. Defined.
Definition rsubZ : Syntax.Expr _ _ _ := Eval vm_compute in proj1_sig rsubZ_sig.
Definition rsubW : Syntax.Expr _ _ _ := Eval vm_compute in rexpr_select_word_sizes rsubZ ExprBinOp_bounds.
Definition rsubZ_Wf : rexpr_wfT rsubZ. Proof. prove_rexpr_wfT. Qed.
Definition rsub_output_bounds
  := Eval vm_compute in compute_bounds rsubZ ExprBinOp_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition rsubZ_correct_and_bounded
  := rexpr_correct_and_bounded rsubZ rsubZ_Wf ExprBinOp_bounds.

Local Open Scope string_scope.
Compute ("Sub", compute_bounds_for_display rsubZ ExprBinOp_bounds).
Compute ("Sub overflows? ", sanity_compute rsubZ ExprBinOp_bounds).
Compute ("Sub overflows (error if it does)? ", sanity_check rsubZ ExprBinOp_bounds).
