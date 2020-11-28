Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.AddGetCarry Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

Module Associational.
  Section Associational.

    Definition sat_multerm s (t t' : (Z * Z)) : list (Z * Z) :=
      dlet_nd xy := Z.mul_split s (snd t) (snd t') in
      [(fst t * fst t', fst xy); (fst t * fst t' * s, snd xy)].

    Definition sat_mul s (p q : list (Z * Z)) : list (Z * Z) :=
      flat_map (fun t => flat_map (fun t' => sat_multerm s t t') q) p.

    Lemma eval_map_sat_multerm s a q (s_nonzero:s<>0):
      Associational.eval (flat_map (sat_multerm s a) q) = fst a * snd a * Associational.eval q.
    Proof using Type.
      cbv [sat_multerm Let_In]; induction q;
        repeat match goal with
               | _ => progress autorewrite with cancel_pair push_eval to_div_mod in *
               | _ => progress simpl flat_map
               | _ => rewrite IHq
               | _ => rewrite Z.mod_eq by assumption
               | _ => ring_simplify; lia
               end.
    Qed.
    Hint Rewrite eval_map_sat_multerm using (lia || assumption) : push_eval.

    Lemma eval_sat_mul s p q (s_nonzero:s<>0):
      Associational.eval (sat_mul s p q) = Associational.eval p * Associational.eval q.
    Proof using Type.
      cbv [sat_mul]; induction p; [reflexivity|].
      repeat match goal with
             | _ => progress (autorewrite with push_flat_map push_eval in * )
             | _ => rewrite IHp
             | _ => ring_simplify; lia
             end.
    Qed.
    Hint Rewrite eval_sat_mul : push_eval.

    Definition sat_multerm_const s (t t' : (Z * Z)) : list (Z * Z) :=
      if snd t =? 1
      then [(fst t * fst t', snd t')]
      else if snd t =? -1
           then [(fst t * fst t', - snd t')]
           else if snd t =? 0
                then nil
                else dlet_nd xy := Z.mul_split s (snd t) (snd t') in
            [(fst t * fst t', fst xy); (fst t * fst t' * s, snd xy)].

    Definition sat_mul_const s (p q : list (Z * Z)) : list (Z * Z) :=
      flat_map (fun t => flat_map (fun t' => sat_multerm_const s t t') q) p.

    Lemma eval_map_sat_multerm_const s a q (s_nonzero:s<>0):
      Associational.eval (flat_map (sat_multerm_const s a) q) = fst a * snd a * Associational.eval q.
    Proof using Type.
      cbv [sat_multerm_const Let_In]; induction q;
        repeat match goal with
               | _ => progress autorewrite with cancel_pair push_eval to_div_mod in *
               | _ => progress simpl flat_map
               | H : _ = 1 |- _ => rewrite H
               | H : _ = -1 |- _ => rewrite H
               | H : _ = 0 |- _ => rewrite H
               | _ => progress break_match; Z.ltb_to_lt
               | _ => rewrite IHq
               | _ => rewrite Z.mod_eq by assumption
               | _ => ring_simplify; lia
               end.
    Qed.
    Hint Rewrite eval_map_sat_multerm_const using (lia || assumption) : push_eval.

    Lemma eval_sat_mul_const s p q (s_nonzero:s<>0):
      Associational.eval (sat_mul_const s p q) = Associational.eval p * Associational.eval q.
    Proof using Type.
      cbv [sat_mul_const]; induction p; [reflexivity|].
      repeat match goal with
             | _ => progress (autorewrite with push_flat_map push_eval in * )
             | _ => rewrite IHp
             | _ => ring_simplify; lia
             end.
    Qed.
    Hint Rewrite eval_sat_mul_const : push_eval.
  End Associational.
End Associational.
