(** * Reflective Pipeline *)
(** This file combines the various PHOAS modules in tactics,
    culminating in a tactic [refine_reflectively], which solves a goal of the form
<<
cast_back_flat_const (?x args) = f (cast_back_flat_const args)
 /\ Bounds.is_bounded_by ?bounds (?x args)
>>
while instantiating [?x] and [?bounds] with nicely-reduced constants.
*)

Ltac refine_reflectively := idtac.

Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Z.Bounds.Interpretation.
Require Import Crypto.Reflection.Z.MapBounds.
Require Import Crypto.Reflection.Z.MapBoundsInterp.
Require Import Crypto.Reflection.Z.Syntax.Util.
Require Import Crypto.Specific.GF25519.
About cast_back_flat_const.

Goal forall var src dst f' V V' f args, exists x bounds, @cast_back_flat_const var dst f' V (x args) = f (@cast_back_flat_const var src f' V' args) /\ Bounds.is_bounded_by bounds (x args).
Proof.
  intros; do 2 eexists.
  refine (let k := MapBoundsPackagedCorrect in _).
