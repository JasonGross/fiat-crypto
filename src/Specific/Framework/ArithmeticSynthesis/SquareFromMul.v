Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.HelperTactics.
Require Crypto.Util.Tuple.

Local Notation tuple := Tuple.tuple.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Infix "^" := tuple : type_scope.

Notation square_sig_type sz m wt :=
  {square : (Z^sz -> Z^sz)%type |
   forall a : Z^sz%nat%type,
     let eval := Positional.Fdecode (m := m) wt in
     Positional.Fdecode (m := m) wt (square a) = (eval a * eval a)%F}
    (only parsing).

Ltac solve_square_sig mul_sig :=
  lazymatch goal with
  | [ |- square_sig_type ?sz ?m ?wt ]
    => idtac;
       let a := fresh "a" in
       eexists; cbv beta zeta; intros a;
       rewrite <-(proj2_sig mul_sig);
       apply f_equal;
       cbv [proj1_sig mul_sig];
       reflexivity
  end.
