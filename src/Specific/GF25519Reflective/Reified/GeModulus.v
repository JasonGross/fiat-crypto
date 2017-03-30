Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rge_modulusZ_sig : rexpr_unop_FEToZ_sig ge_modulus. Proof. reify_sig. Defined.
Definition rge_modulusZ : Expr _ := Eval vm_compute in proj1_sig rge_modulusZ_sig.
Definition rge_modulusW_pkgo := Eval vm_compute in rexpr_select_word_sizes_option rge_modulusZ ExprUnOpFEToZ_bounds.
Definition rge_modulusW_pkg := Eval vm_compute in rexpr_select_word_sizes_postprocess1 rge_modulusW_pkgo.
Definition rge_modulusT := get_output_type rge_modulusW_pkg.
Definition rge_modulusW' : Expr _ := Eval vm_compute in get_output_expr rge_modulusW_pkg.
Definition rge_modulusW : Expr rge_modulusT := Eval cbv [rge_modulusW'] in rexpr_select_word_sizes_postprocess2 rge_modulusW'.
Definition rge_modulus_output_bounds := Eval vm_compute in get_bounds rge_modulusW_pkg.
Definition rge_modulusZ_Wf : rexpr_wfT rge_modulusZ. Proof. prove_rexpr_wfT. Qed.
Local Obligation Tactic := rexpr_correct_and_bounded_obligation_tac.
Program Definition rge_modulusZ_correct_and_bounded_tight
  : rexpr_correct_and_boundedT rge_modulusZ rge_modulusW ExprUnOpFEToZ_bounds rge_modulus_output_bounds
  := rexpr_correct_and_bounded rge_modulusZ rge_modulusW ExprUnOpFEToZ_bounds rge_modulus_output_bounds rge_modulusZ_Wf.

Local Open Scope string_scope.
Compute ("Ge_Modulus", compute_bounds_for_display rge_modulusW_pkg).
(* We use [compute] rather than [vm_compute] so as to not eta-expand functions, so we get pretty display *)
Eval compute in ("Ge_Modulus overflows? ", sanity_compute rge_modulusW_pkg).
Compute ("Ge_Modulus overflows (error if it does)? ", sanity_check rge_modulusW_pkg).
