Require Import Crypto.SpecificGen.GF2213_32Reflective.Common.

Definition roppZ_sig : rexpr_unop_sig opp. Proof. reify_sig. Defined.
Definition roppZ : Syntax.Expr _ _ _ := Eval vm_compute in proj1_sig roppZ_sig.
Definition roppW : Syntax.Expr _ _ _ := Eval vm_compute in rexpr_select_word_sizes roppZ ExprUnOp_bounds.
Definition roppZ_Wf : rexpr_wfT roppZ. Proof. prove_rexpr_wfT. Qed.
Definition ropp_output_bounds
  := Eval vm_compute in compute_bounds roppZ ExprUnOp_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition roppZ_correct_and_bounded
  := rexpr_correct_and_bounded roppZ roppZ_Wf ExprUnOp_bounds.

Local Open Scope string_scope.
Compute ("Opp", compute_bounds_for_display roppZ ExprUnOp_bounds).
Compute ("Opp overflows? ", sanity_compute roppZ ExprUnOp_bounds).
Compute ("Opp overflows (error if it does)? ", sanity_check roppZ ExprUnOp_bounds).
