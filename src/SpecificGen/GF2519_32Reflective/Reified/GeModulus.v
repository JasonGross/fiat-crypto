Require Import Crypto.SpecificGen.GF2519_32Reflective.Common.

Definition rge_modulusZ_sig : rexpr_unop_FEToZ_sig ge_modulus. Proof. reify_sig. Defined.
Definition rge_modulusZ : Syntax.Expr _ _ _ := Eval vm_compute in proj1_sig rge_modulusZ_sig.
Definition rge_modulusW : Syntax.Expr _ _ _ := Eval vm_compute in rexpr_select_word_sizes rge_modulusZ ExprUnOpFEToZ_bounds.
Definition rge_modulusZ_Wf : rexpr_wfT rge_modulusZ. Proof. prove_rexpr_wfT. Qed.
Definition rge_modulus_output_bounds
  := Eval vm_compute in compute_bounds rge_modulusZ ExprUnOpFEToZ_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition rge_modulusZ_correct_and_bounded
  := rexpr_correct_and_bounded rge_modulusZ rge_modulusZ_Wf ExprUnOpFEToZ_bounds.

Local Open Scope string_scope.
Compute ("Ge_Modulus", compute_bounds_for_display rge_modulusZ ExprUnOpFEToZ_bounds).
Compute ("Ge_Modulus overflows? ", sanity_compute rge_modulusZ ExprUnOpFEToZ_bounds).
Compute ("Ge_Modulus overflows (error if it does)? ", sanity_check rge_modulusZ ExprUnOpFEToZ_bounds).
