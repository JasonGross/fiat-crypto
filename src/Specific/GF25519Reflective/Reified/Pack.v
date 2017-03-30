Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rpackZ_sig : rexpr_unop_FEToWire_sig pack. Proof. reify_sig. Defined.
Definition rpackZ : Expr _ := Eval vm_compute in proj1_sig rpackZ_sig.
Definition rpackW_pkgo := Eval vm_compute in rexpr_select_word_sizes_option rpackZ ExprUnOpFEToWire_bounds.
Definition rpackW_pkg := Eval vm_compute in rexpr_select_word_sizes_postprocess1 rpackW_pkgo.
Definition rpackT := get_output_type rpackW_pkg.
Definition rpackW' : Expr _ := Eval vm_compute in get_output_expr rpackW_pkg.
Definition rpackW : Expr rpackT := Eval cbv [rpackW'] in rexpr_select_word_sizes_postprocess2 rpackW'.
Definition rpack_output_bounds := Eval vm_compute in get_bounds rpackW_pkg.
Definition rpackZ_Wf : rexpr_wfT rpackZ. Proof. prove_rexpr_wfT. Qed.
Local Obligation Tactic := rexpr_correct_and_bounded_obligation_tac.
Program Definition rpackZ_correct_and_bounded_tight
  : rexpr_correct_and_boundedT rpackZ rpackW ExprUnOpFEToWire_bounds rpack_output_bounds
  := rexpr_correct_and_bounded rpackZ rpackW ExprUnOpFEToWire_bounds rpack_output_bounds rpackZ_Wf.

Local Open Scope string_scope.
Compute ("Pack", compute_bounds_for_display rpackW_pkg).
(* We use [compute] rather than [vm_compute] so as to not eta-expand functions, so we get pretty display *)
Eval compute in ("Pack overflows? ", sanity_compute rpackW_pkg).
Compute ("Pack overflows (error if it does)? ", sanity_check rpackW_pkg).
