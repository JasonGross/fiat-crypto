(* Following http://adam.chlipala.net/theses/andreser.pdf chapter 3 *)
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Structures.Orders.
Require Import Coq.Lists.List.
Require Import Crypto.Algebra.Nsatz.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Decidable.Bool2Prop.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Modulo.PullPush.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

Module Weight.
  Section Weight.
    Context weight
            (weight_0 : weight 0%nat = 1)
            (weight_positive : forall i, 0 < weight i)
            (weight_multiples : forall i, weight (S i) mod weight i = 0)
            (weight_divides : forall i : nat, 0 < weight (S i) / weight i).

    Lemma weight_multiples_full' j : forall i, weight (i+j) mod weight i = 0.
    Proof using weight_positive weight_multiples.
      induction j; intros;
        repeat match goal with
               | _ => rewrite Nat.add_succ_r
               | _ => rewrite IHj
               | |- context [weight (S ?x) mod weight _] =>
                 rewrite (Z.div_mod (weight (S x)) (weight x)), weight_multiples by auto with zarith
               | _ => progress autorewrite with push_Zmod natsimplify zsimplify_fast
               | _ => reflexivity
               end.
    Qed.

    Lemma weight_multiples_full j i : (i <= j)%nat -> weight j mod weight i = 0.
    Proof using weight_positive weight_multiples.
      intros; replace j with (i + (j - i))%nat by lia.
      apply weight_multiples_full'.
    Qed.

    Lemma weight_divides_full j i : (i <= j)%nat -> 0 < weight j / weight i.
    Proof using weight_positive weight_multiples. auto using Z.gt_lt, Z.div_positive_gt_0, weight_multiples_full with zarith. Qed.

    Lemma weight_div_mod j i : (i <= j)%nat -> weight j = weight i * (weight j / weight i).
    Proof using weight_positive weight_multiples. intros. apply Z.div_exact; auto using weight_multiples_full with zarith. Qed.

    Lemma weight_mod_pull_div n x :
      x mod weight (S n) / weight n =
      (x / weight n) mod (weight (S n) / weight n).
    Proof using weight_positive weight_multiples weight_divides.
      replace (weight (S n)) with (weight n * (weight (S n) / weight n));
      repeat match goal with
             | _ => progress autorewrite with zsimplify_fast
             | _ => rewrite Z.mul_div_eq_full by auto with zarith
             | _ => rewrite Z.mul_div_eq' by auto with zarith
             | _ => rewrite Z.mod_pull_div
             | _ => rewrite weight_multiples by auto with zarith
             | _ => solve [auto with zarith]
             end.
    Qed.

    Lemma weight_div_pull_div n x :
      x / weight (S n) =
      (x / weight n) / (weight (S n) / weight n).
    Proof using weight_positive weight_multiples weight_divides.
      replace (weight (S n)) with (weight n * (weight (S n) / weight n));
      repeat match goal with
             | _ => progress autorewrite with zdiv_to_mod zsimplify_fast
             | _ => rewrite Z.mul_div_eq_full by auto with zarith
             | _ => rewrite Z.mul_div_eq' by auto with zarith
             | _ => rewrite Z.div_div by auto with zarith
             | _ => rewrite weight_multiples by assumption
             | _ => solve [auto with zarith]
             end.
    Qed.
  End Weight.
End Weight.

Record weight_properties {weight : nat -> Z} :=
  {
    weight_0 : weight 0%nat = 1;
    weight_positive : forall i, 0 < weight i;
    weight_multiples : forall i, weight (S i) mod weight i = 0;
    weight_divides : forall i : nat, 0 < weight (S i) / weight i;
  }.
Hint Resolve weight_0 weight_positive weight_multiples weight_divides : core.
Lemma weight_nz {weight : nat -> Z} {wprops : @weight_properties weight}
  : forall i, weight i <> 0.
Proof. intro i; pose proof (@weight_positive _ wprops i); lia. Qed.
Hint Resolve weight_nz : core.
