Require Export Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Export Coq.Lists.List. Export ListNotations.
Require Export Crypto.Arithmetic.Core. Export B.
Require Export Crypto.Arithmetic.PrimeFieldTheorems.
Require Export Crypto.Arithmetic.Saturated.Freeze.
Require Export Crypto.Specific.Framework.CurveParameters.
Require Export Crypto.Specific.Framework.ArithmeticSynthesis.HelperTactics.
Require Export Crypto.Util.Decidable.
Require Export Crypto.Util.LetIn Crypto.Util.ZUtil.
Require Export Crypto.Util.Tactics.BreakMatch.
Require Export Crypto.Util.Decidable.
Require Crypto.Util.Tuple.
Require Export Crypto.Util.QUtil.

Module Export Exports.
  Export CurveParameters.Notations.
  Export Coq.setoid_ring.ZArithRing.
End Exports.

Section wt.
  Import QArith Qround.
  Local Coercion QArith_base.inject_Z : Z >-> Q.
  Local Coercion Z.of_nat : nat >-> Z.
  Definition wt_gen (m : positive) (sz : nat) (i:nat) : Z := 2^Qceiling((Z.log2_up m/sz)*i).
End wt.

Ltac solve_constant_sig :=
  idtac;
  lazymatch goal with
  | [ |- { c : Z^?sz | Positional.Fdecode (m:=?M) ?wt c = ?v } ]
    => let t := (eval vm_compute in
                    (Positional.encode (n:=sz) (modulo:=modulo) (div:=div) wt (F.to_Z (m:=M) v))) in
       (exists t; vm_decide)
  end.

Ltac destruct_and_in H :=
  lazymatch type of H with
  | True => destruct H
  | and _ _ => let maybe_H := fresh H in
               let probably_not_H := fresh maybe_H in
               let not_H := fresh probably_not_H in
               let H1 := fresh not_H in
               let H2 := fresh H1 in
               destruct H as [H1 H2];
               destruct_and_in H1; destruct_and_in H2
  | _ => idtac
  end.
