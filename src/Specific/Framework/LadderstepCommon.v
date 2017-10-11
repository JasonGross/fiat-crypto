Require Import Coq.ZArith.BinIntDef.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Curves.Montgomery.XZ.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.

(** TODO(jadep,andreser): Move to NewBaseSystemTest? *)
Definition FMxzladderstep {m} := @M.donnaladderstep (F m) F.add F.sub F.mul.

Section with_notations.
  Context sz (add sub mul : tuple Z sz -> tuple Z sz -> tuple Z sz)
          (square carry : tuple Z sz -> tuple Z sz).
  Local Infix "+" := add.
  Local Notation "a * b" := (carry (mul a b)).
  Local Notation "x ^ 2" := (carry (square x)).
  Local Infix "-" := sub.
  Definition Mxzladderstep a24 x1 Q Q'
    := match Q, Q' with
       | (x, z), (x', z') =>
         dlet origx := x in
         dlet x := x + z in
         dlet z := origx - z in
         dlet origx' := x' in
         dlet x' := x' + z' in
         dlet z' := origx' - z' in
         dlet xx' := x' * z in
         dlet zz' := x * z' in
         dlet origx' := xx' in
         dlet xx' := xx' + zz' in
         dlet zz' := origx' - zz' in
         dlet x3 := xx'^2 in
         dlet zzz' := zz'^2 in
         dlet z3 := zzz' * x1 in
         dlet xx := x^2 in
         dlet zz := z^2 in
         dlet x2 := xx * zz in
         dlet zz := xx - zz in
         dlet zzz := zz * a24 in
         dlet zzz := zzz + xx in
         dlet z2 := zz * zzz in
         ((x2, z2), (x3, z3))%core
       end.
End with_notations.
