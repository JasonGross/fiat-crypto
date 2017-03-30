Require Import Crypto.SpecificGen.GF2213_32Reflective.Common.

Definition rpackZ_sig : rexpr_unop_FEToWire_sig pack. Proof. reify_sig. Defined.
Definition rpackZ : Syntax.Expr _ _ _ := Eval vm_compute in proj1_sig rpackZ_sig.
Definition rpackW : Syntax.Expr _ _ _ := Eval vm_compute in rexpr_select_word_sizes rpackZ ExprUnOpFEToWire_bounds.
Definition rpackZ_Wf : rexpr_wfT rpackZ. Proof. prove_rexpr_wfT. Qed.
Definition rpack_output_bounds
  := Eval vm_compute in compute_bounds rpackZ ExprUnOpFEToWire_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition rpackZ_correct_and_bounded
  := rexpr_correct_and_bounded rpackZ rpackZ_Wf ExprUnOpFEToWire_bounds.

Local Open Scope string_scope.
Compute ("Pack", compute_bounds_for_display rpackZ ExprUnOpFEToWire_bounds).
Compute ("Pack overflows? ", sanity_compute rpackZ ExprUnOpFEToWire_bounds).
Compute ("Pack overflows (error if it does)? ", sanity_check rpackZ ExprUnOpFEToWire_bounds).
