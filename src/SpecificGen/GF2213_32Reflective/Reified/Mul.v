Require Import Crypto.SpecificGen.GF2213_32Reflective.Common.

Definition rmulZ_sig : rexpr_binop_sig mul. Proof. reify_sig. Defined.
Definition rmulZ : Syntax.Expr _ _ _ := Eval vm_compute in proj1_sig rmulZ_sig.
Definition rmulW : Syntax.Expr _ _ _ := Eval vm_compute in rexpr_select_word_sizes rmulZ ExprBinOp_bounds.
Definition rmulZ_Wf : rexpr_wfT rmulZ. Proof. prove_rexpr_wfT. Qed.
Definition rmul_output_bounds
  := Eval vm_compute in compute_bounds rmulZ ExprBinOp_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition rmulZ_correct_and_bounded
  := rexpr_correct_and_bounded rmulZ rmulZ_Wf ExprBinOp_bounds.

Local Open Scope string_scope.
Compute ("Mul", compute_bounds_for_display rmulZ ExprBinOp_bounds).
Compute ("Mul overflows? ", sanity_compute rmulZ ExprBinOp_bounds).
Compute ("Mul overflows (error if it does)? ", sanity_check rmulZ ExprBinOp_bounds).
