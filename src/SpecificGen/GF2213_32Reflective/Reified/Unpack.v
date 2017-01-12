Require Import Crypto.SpecificGen.GF2213_32Reflective.Common.

Definition runpackZ_sig : rexpr_unop_WireToFE_sig unpack. Proof. reify_sig. Defined.
Definition runpackZ : Syntax.Expr _ _ _ := Eval vm_compute in proj1_sig runpackZ_sig.
Definition runpackW : Syntax.Expr _ _ _ := Eval vm_compute in rexpr_select_word_sizes runpackZ ExprUnOpWireToFE_bounds.
Definition runpackZ_Wf : rexpr_wfT runpackZ. Proof. prove_rexpr_wfT. Qed.
Definition runpack_output_bounds
  := Eval vm_compute in compute_bounds runpackZ ExprUnOpWireToFE_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition runpackZ_correct_and_bounded
  := rexpr_correct_and_bounded runpackZ runpackZ_Wf ExprUnOpWireToFE_bounds.

Local Open Scope string_scope.
Compute ("Unpack", compute_bounds_for_display runpackZ ExprUnOpWireToFE_bounds).
Compute ("Unpack overflows? ", sanity_compute runpackZ ExprUnOpWireToFE_bounds).
Compute ("Unpack overflows (error if it does)? ", sanity_check runpackZ ExprUnOpWireToFE_bounds).
