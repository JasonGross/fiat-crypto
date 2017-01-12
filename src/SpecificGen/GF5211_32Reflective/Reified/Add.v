Require Export Crypto.SpecificGen.GF5211_32Reflective.Common.
Require Export Crypto.Reflection.Z.Interpretations.
(*Require Import Crypto.SpecificGen.GF5211_32Reflective.CommonBinOp.*)

Definition raddZ_sig : rexpr_binop_sig add. Proof. reify_sig. Defined.

Notation bounded_sig rexprZ_sig expr_bounds
  := { expr : Syntax.Expr _ _ _ _ | expr = Bounds.MapBounds (proj1_sig rexprZ_sig) expr_bounds }.
Notation make_bounded_sig rexprZ_sig expr_bounds
  := (let k := Bounds.MapBounds (proj1_sig rexprZ_sig) expr_bounds in
      exist (fun expr => expr = k) k eq_refl).
Notation compute_bounds rexprZ_sig expr_bounds
  := (Bounds.ComputeBounds (proj1_sig rexprZ_sig) ExprBinOp_bounds).

Time Definition raddBounds_sig : bounded_sig raddZ_sig ExprBinOp_bounds
  := Eval vm_compute in make_bounded_sig raddZ_sig ExprBinOp_bounds.
Definition raddW : Expr _ := Eval cbv [proj1_sig raddBounds_sig] in proj1_sig raddBounds_sig.
Definition radd_output_bounds := Eval vm_compute in compute_bounds raddZ_sig ExprBinOp_bounds.

(*Import Reflection.Syntax.
Compute proj1_sig raddZ_sig.
Require Import Reflection.MapCastWithCastOp.
Require Import Reflection.MapInterp.
Goal True.
  pose (proj1_sig raddZ_sig) as e.
  let T := type of e in
  vm_compute in e;
    change T in (type of e).
  refine (let k := fun var
                   => @map_interp_cast_with_cast_op
                        base_type base_type interp_base_type Bounds.interp_base_type
                        op op (@Bounds.interp_op)
                        base_type_beq internal_base_type_dec_bl (fun _ => ZToInterp 0)
                        (fun _ => Bounds.bounds_to_base_type)
                        (fun _ _ v _ => cast_const v)
                        (fun _ _ _ => Op (Cast _ _))
                        (fun _ _ opc => match opc with Cast _ _ => true | _ => false end)
                        (@Bounds.bound_op)
                        var
                        _ (e _)
                        _ (MapInterp (@Bounds.of_interp) e _)
                        (Application.interp_all_binders_for_to' ExprBinOp_bounds)
          in _);
    cbv beta in k.
let T' := type of k in set (T := MapCast.new_type _ _ _ _) in k.
vm_compute in T.
subst T.
Timeout 5 let T := type of k in
vm_compute in k;
change T in (type of k).
set (T := Application.interp_all_binders_for' _ _) in k.
compute in T.
pose ().
unfold Application.interp_all_binders_for', ExprBinOpT in k.
(MapInterp (@ZBounds.of_wordW) opW))
  (ApplyInterpedAll (Interp (@ZBounds.interp_op) (MapInterp (@ZBounds.of_wordW) opW)) bounds)
  simpl in k.
  let T := type of e in set (T' := T) in e.

Definition raddW := Eval vm_compute in rword_of_Z raddZ_sig.
Lemma raddW_correct_and_bounded_gen : correct_and_bounded_genT raddW raddZ_sig.
Proof. rexpr_correct. Qed.
Definition radd_output_bounds := Eval vm_compute in compute_bounds raddW ExprBinOp_bounds.

Local Open Scope string_scope.
Compute ("Add", compute_bounds_for_display raddW ExprBinOp_bounds).
Compute ("Add overflows? ", sanity_compute raddW ExprBinOp_bounds).
Compute ("Add overflows (error if it does)? ", sanity_check raddW ExprBinOp_bounds).
*)
