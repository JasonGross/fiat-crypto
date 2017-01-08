Require Export Crypto.Specific.GF25519Reflective.Common.
Require Export Crypto.Reflection.Z.Interpretations.
(*Require Import Crypto.Specific.GF25519Reflective.CommonBinOp.*)

Definition rmulZ_sig : rexpr_binop_sig mul. Proof. reify_sig. Defined.
Import Reflection.Syntax.
Compute proj1_sig rmulZ_sig.
Require Import Reflection.MapCastWithCastOp.
Require Import Reflection.MapInterp.
Goal True.
  pose (proj1_sig rmulZ_sig) as e.
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

Definition rmulW := Eval vm_compute in rword_of_Z rmulZ_sig.
Lemma rmulW_correct_and_bounded_gen : correct_and_bounded_genT rmulW rmulZ_sig.
Proof. rexpr_correct. Qed.
Definition rmul_output_bounds := Eval vm_compute in compute_bounds rmulW ExprBinOp_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition rmulW_correct_and_bounded
  := ExprBinOp_correct_and_bounded
       rmulW mul rmulZ_sig rmulW_correct_and_bounded_gen
       _ _.

Local Open Scope string_scope.
Compute ("Mul", compute_bounds_for_display rmulW ExprBinOp_bounds).
Compute ("Mul overflows? ", sanity_compute rmulW ExprBinOp_bounds).
Compute ("Mul overflows (error if it does)? ", sanity_check rmulW ExprBinOp_bounds).
