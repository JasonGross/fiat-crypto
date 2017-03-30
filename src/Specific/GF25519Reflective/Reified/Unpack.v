Require Import Crypto.Specific.GF25519Reflective.Common.

Definition runpackZ_sig : rexpr_unop_WireToFE_sig unpack. Proof. reify_sig. Defined.
Definition runpackZ : Expr _ := Eval vm_compute in proj1_sig runpackZ_sig.
Definition runpackW_pkgo := Eval vm_compute in rexpr_select_word_sizes_option runpackZ ExprUnOpWireToFE_bounds.
Definition runpackW_pkg := Eval vm_compute in rexpr_select_word_sizes_postprocess1 runpackW_pkgo.
Definition runpackT := get_output_type runpackW_pkg.
Definition runpackW' : Expr _ := Eval vm_compute in get_output_expr runpackW_pkg.
Definition runpackW : Expr runpackT := Eval cbv [runpackW'] in rexpr_select_word_sizes_postprocess2 runpackW'.
Definition runpack_output_bounds := Eval vm_compute in get_bounds runpackW_pkg.
Definition runpackZ_Wf : rexpr_wfT runpackZ. Proof. prove_rexpr_wfT. Qed.
Local Obligation Tactic := rexpr_correct_and_bounded_obligation_tac.
Program Definition runpackZ_correct_and_bounded_tight
  : rexpr_correct_and_boundedT runpackZ runpackW ExprUnOpWireToFE_bounds runpack_output_bounds
  := rexpr_correct_and_bounded runpackZ runpackW ExprUnOpWireToFE_bounds runpack_output_bounds runpackZ_Wf.

Local Open Scope string_scope.
Compute ("Unpack", compute_bounds_for_display runpackW_pkg).
(* We use [compute] rather than [vm_compute] so as to not eta-expand functions, so we get pretty display *)
Eval compute in ("Unpack overflows? ", sanity_compute runpackW_pkg).
Compute ("Unpack overflows (error if it does)? ", sanity_check runpackW_pkg).
