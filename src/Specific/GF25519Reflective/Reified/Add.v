Require Export Crypto.Specific.GF25519Reflective.Common.
Require Export Crypto.Reflection.Z.Interpretations.
(*Require Import Crypto.Specific.GF25519Reflective.CommonBinOp.*)

Definition raddZ_sig : rexpr_binop_sig add. Proof. reify_sig. Defined.
Import Reflection.Syntax.
Compute proj1_sig raddZ_sig.
Require Import Reflection.MapCastWithCastOp.
Goal True.
  pose (proj1_sig raddZ_sig) as e.
  let T := type of e in
  vm_compute in e;
    change T in (type of e).
  refine (let k := @map_interp_cast_with_cast_op
                     base_type base_type interp_base_type  in _).

  let T := type of e in set (T' := T) in e.

Definition raddW := Eval vm_compute in rword_of_Z raddZ_sig.
Lemma raddW_correct_and_bounded_gen : correct_and_bounded_genT raddW raddZ_sig.
Proof. rexpr_correct. Qed.
Definition radd_output_bounds := Eval vm_compute in compute_bounds raddW ExprBinOp_bounds.

Local Open Scope string_scope.
Compute ("Add", compute_bounds_for_display raddW ExprBinOp_bounds).
Compute ("Add overflows? ", sanity_compute raddW ExprBinOp_bounds).
Compute ("Add overflows (error if it does)? ", sanity_check raddW ExprBinOp_bounds).
