Require Export Crypto.Specific.GF25519Reflective.Common.
Require Export Crypto.Reflection.Z.Interpretations.
(*Require Import Crypto.Specific.GF25519Reflective.CommonBinOp.*)

Definition rmulZ_sig : rexpr_binop_sig mul. Proof. reify_sig. Time Defined.
Definition rmulZ := Eval vm_compute in proj1_sig rmulZ_sig.

Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.MapCastWithCastOp.
Require Import Crypto.Reflection.MapInterp.
Time Definition rmulW' : Expr base_type interp_base_type op _
  := let e := proj1_sig rmulZ_sig in
     let k := fun var
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
                   (Application.interp_all_binders_for_to' ExprBinOp_bounds) in
     k.
Time Definition rmulW : Expr base_type interp_base_type op _
  := Eval vm_compute in rmulW'.
(*Import Reflection.Syntax.
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
Require Import Bedrock.Word.
Notation "a '*64' b" := (Op (Mul (TWord 6)) (Pair a b)) (at level 50).
Notation "a '*32' b" := (Op (Mul (TWord 5)) (Pair a b)) (at level 50).
Notation "'(uint32_t)' x" := (Op (Cast _ (TWord 5)) x) (at level 0).
Notation "'(uint64_t)' x" := (Op (Cast _ (TWord 6)) x) (at level 0).
Infix "*32" := (Op (Mul (TWord 5))) (at level 50).
Definition rmulW := Eval vm_compute in rword_of_Z rmulZ_sig.

Lemma rmulZ_correct_and_bounded_gen : correct_and_bounded_genT rmulZ rmulZ_sig.
Proof. rexpr_correct. Qed.
Definition rmul_output_bounds := Eval vm_compute in compute_bounds rmulZ ExprBinOp_bounds.
Local Obligation Tactic := intros; vm_compute; constructor.
Program Definition rmulZ_correct_and_bounded
  := ExprBinOp_correct_and_bounded
       rmulZ mul rmulZ_sig rmulZ_correct_and_bounded_gen
       _ _.

Local Open Scope string_scope.
Compute ("Mul", compute_bounds_for_display rmulZ ExprBinOp_bounds).
Compute ("Mul overflows? ", sanity_compute rmulZ ExprBinOp_bounds).
Compute ("Mul overflows (error if it does)? ", sanity_check rmulZ ExprBinOp_bounds).
*)
