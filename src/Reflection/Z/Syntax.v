(** * PHOAS Syntax for expression trees on ℤ *)
Require Import Coq.ZArith.ZArith.
Require Import Bedrock.Word.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.ModularArithmetic.ModularBaseSystemListZOperations.
Require Import Crypto.Util.Equality.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.PartiallyReifiedProp.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Util.Tactics.
Export Syntax.Notations.

Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.
Scheme Equality for Z.
Inductive base_type := TZ | TWord (logsz : nat).
Definition interp_base_type (v : base_type) : Type :=
  match v with
  | TZ => Z
  | TWord logsz => wordT logsz
  end.


Definition interpToZ {t} : interp_base_type t -> Z
  := match t with
     | TZ => fun x => x
     | TWord _ => wordToZ
     end.
Definition ZToInterp {t} : Z -> interp_base_type t
  := match t return Z -> interp_base_type t with
     | TZ => fun x => x
     | TWord _ => ZToWord
     end.
Definition cast_const {t1 t2} (v : interp_base_type t1) : interp_base_type t2
  := ZToInterp (interpToZ v).

Global Instance dec_eq_base_type : DecidableRel (@eq base_type)
  := base_type_eq_dec.
Global Instance dec_eq_flat_type : DecidableRel (@eq (flat_type base_type)) := _.
Global Instance dec_eq_type : DecidableRel (@eq (type base_type)) := _.

Local Notation tZ := (Tbase TZ).
Local Notation eta x := (fst x, snd x).
Local Notation eta3 x := (eta (fst x), snd x).
Local Notation eta4 x := (eta3 (fst x), snd x).

Inductive op : flat_type base_type -> flat_type base_type -> Type :=
| Add T : op (Tbase T * Tbase T) (Tbase T)
| Sub T : op (Tbase T * Tbase T) (Tbase T)
| Mul T : op (Tbase T * Tbase T) (Tbase T)
| Shl T : op (Tbase T * Tbase T) (Tbase T)
| Shr T : op (Tbase T * Tbase T) (Tbase T)
| Land T : op (Tbase T * Tbase T) (Tbase T)
| Lor T : op (Tbase T * Tbase T) (Tbase T)
| Neg T (int_width : Z) : op (Tbase T) (Tbase T)
| Cmovne T : op (Tbase T * Tbase T * Tbase T * Tbase T) (Tbase T)
| Cmovle T : op (Tbase T * Tbase T * Tbase T * Tbase T) (Tbase T)
| Cast T1 T2 : op (Tbase T1) (Tbase T2).

Definition interp_op src dst (f : op src dst) : interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst
  := match f in op src dst return interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst with
     | Add TZ => fun xy => fst xy + snd xy
     | Sub TZ => fun xy => fst xy - snd xy
     | Mul TZ => fun xy => fst xy * snd xy
     | Shl TZ => fun xy => fst xy << snd xy
     | Shr TZ => fun xy => fst xy >> snd xy
     | Land TZ => fun xy => Z.land (fst xy) (snd xy)
     | Lor TZ => fun xy => Z.lor (fst xy) (snd xy)
     | Neg TZ int_width => fun x => ModularBaseSystemListZOperations.neg int_width x
     | Cmovne TZ => fun xyzw => let '(x, y, z, w) := eta4 xyzw in cmovne x y z w
     | Cmovle TZ => fun xyzw => let '(x, y, z, w) := eta4 xyzw in cmovl x y z w
     | Add _ => fun xy => wadd (fst xy) (snd xy)
     | Sub _ => fun xy => wsub (fst xy) (snd xy)
     | Mul _ => fun xy => wmul (fst xy) (snd xy)
     | Shl _ => fun xy => wshl (fst xy) (snd xy)
     | Shr _ => fun xy => wshr (fst xy) (snd xy)
     | Land _ => fun xy => wland (fst xy) (snd xy)
     | Lor _ => fun xy => wlor (fst xy) (snd xy)
     | Neg _ int_width => fun x => ModularBaseSystemListZOperations.wneg int_width x
     | Cmovne _ => fun xyzw => let '(x, y, z, w) := eta4 xyzw in wcmovne x y z w
     | Cmovle _ => fun xyzw => let '(x, y, z, w) := eta4 xyzw in wcmovl x y z w
     | Cast _ _ => cast_const
     end%Z.

Definition base_type_eq_semidec_transparent (t1 t2 : base_type)
  : option (t1 = t2)
  := match base_type_eq_dec t1 t2 with
     | left pf => Some pf
     | right _ => None
     end.
Lemma base_type_eq_semidec_is_dec t1 t2 : base_type_eq_semidec_transparent t1 t2 = None -> t1 <> t2.
Proof.
  unfold base_type_eq_semidec_transparent; break_match; congruence.
Qed.

Definition op_beq_hetero {t1 tR t1' tR'} (f : op t1 tR) (g : op t1' tR') : bool
  := match f, g return bool with
     | Add T1, Add T2
     | Sub T1, Sub T2
     | Mul T1, Mul T2
     | Shl T1, Shl T2
     | Shr T1, Shr T2
     | Land T1, Land T2
     | Lor T1, Lor T2
     | Cmovne T1, Cmovne T2
     | Cmovle T1, Cmovle T2
       => base_type_beq T1 T2
     | Neg T1 n, Neg T2 m
       => base_type_beq T1 T2 && Z.eqb n m
     | Cast T1 T2, Cast T1' T2'
       => base_type_beq T1 T1' && base_type_beq T2 T2'
     | Add _, _ => false
     | Sub _, _ => false
     | Mul _, _ => false
     | Shl _, _ => false
     | Shr _, _ => false
     | Land _, _ => false
     | Lor _, _ => false
     | Neg _ _, _ => false
     | Cmovne _, _ => false
     | Cmovle _, _ => false
     | Cast _ _, _ => false
     end%bool.

Definition op_beq t1 tR (f g : op t1 tR) : bool
  := Eval cbv [op_beq_hetero] in op_beq_hetero f g.

Definition op_beq_hetero_type_eq {t1 tR t1' tR'} f g : to_prop (@op_beq_hetero t1 tR t1' tR' f g) -> t1 = t1' /\ tR = tR'.
Proof.
  destruct f, g;
    repeat match goal with
           | _ => progress unfold op_beq_hetero in *
           | _ => simpl; intro; exfalso; assumption
           | _ => solve [ repeat constructor ]
           | _ => progress destruct_head base_type
           | [ |- context[reified_Prop_of_bool ?b] ]
             => let H := fresh in destruct (Sumbool.sumbool_of_bool b) as [H|H]; rewrite H
           | [ H : nat_beq _ _ = true |- _ ] => apply internal_nat_dec_bl in H; subst
           | [ H : andb ?x ?y = true |- _ ]
             => assert (x = true /\ y = true) by (destruct x, y; simpl in *; repeat constructor; exfalso; clear -H; abstract congruence);
                  clear H
           | [ H : and _ _ |- _ ] => destruct H
           | [ H : false = true |- _ ] => exfalso; clear -H; abstract congruence
           | [ H : true = false |- _ ] => exfalso; clear -H; abstract congruence
           end.
Defined.

Definition op_beq_hetero_type_eqs {t1 tR t1' tR'} f g : to_prop (@op_beq_hetero t1 tR t1' tR' f g) -> t1 = t1'
  := fun H => let (p, q) := @op_beq_hetero_type_eq t1 tR t1' tR' f g H in p.
Definition op_beq_hetero_type_eqd {t1 tR t1' tR'} f g : to_prop (@op_beq_hetero t1 tR t1' tR' f g) -> tR = tR'
  := fun H => let (p, q) := @op_beq_hetero_type_eq t1 tR t1' tR' f g H in q.

Definition op_beq_hetero_eq {t1 tR t1' tR'} f g
  : forall pf : to_prop (@op_beq_hetero t1 tR t1' tR' f g),
    eq_rect
      _ (fun src => op src tR')
      (eq_rect _ (fun dst => op t1 dst) f _ (op_beq_hetero_type_eqd f g pf))
      _ (op_beq_hetero_type_eqs f g pf)
    = g.
Proof.
  destruct f, g;
    repeat match goal with
           | _ => solve [ intros [] ]
           | _ => reflexivity
           | [ H : False |- _ ] => exfalso; assumption
           | _ => intro
           | [ |- context[op_beq_hetero_type_eqd ?f ?g ?pf] ]
             => generalize (op_beq_hetero_type_eqd f g pf), (op_beq_hetero_type_eqs f g pf)
           | _ => intro
           | _ => progress eliminate_hprop_eq
           | [ H : Tbase _ = Tbase _ |- _ ] => inversion H; progress subst
           | _ => progress unfold op_beq_hetero in *
           | _ => progress simpl in *
           | [ H : context[andb ?x ?y] |- _ ]
             => destruct x eqn:?, y eqn:?; simpl in H
           | [ H : Z.eqb _ _ = true |- _ ] => apply Z.eqb_eq in H
           | _ => progress subst
           end.
Qed.

Lemma op_beq_bl : forall t1 tR x y, to_prop (op_beq t1 tR x y) -> x = y.
Proof.
  intros ?? f g H.
  pose proof (op_beq_hetero_eq f g H) as H'.
  generalize dependent (op_beq_hetero_type_eqd f g H).
  generalize dependent (op_beq_hetero_type_eqs f g H).
  intros; eliminate_hprop_eq; simpl in *; assumption.
Qed.
