Require Import Coq.Classes.Morphisms.

Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.BoundedWord.
Require Import Crypto.Specific.IntegrationTestTemporaryMiscCommon.
Require Import Crypto.Compilers.Z.Bounds.Pipeline.
Require Import Crypto.Specific.ArithmeticSynthesisFramework.

Require Import Crypto.Util.FixedWordSizes.
Require Import Coq.ZArith.BinIntDef.
Require Import Crypto.Curves.Montgomery.XZ.
Require Import Crypto.Specific.ArithmeticSynthesisReflectiveFramework.
Require Import Crypto.Util.Sigma.MapProjections Crypto.Util.Sigma.Lift.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.MoveLetIn.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.Tactics.ETransitivity.
Require Import Crypto.Util.Notations.

Section with_package.
  Context (package : ArithmeticSynthesisTestPackage).

  Local Notation add_sig := (@add_sig _ package).
  Local Notation mul_sig := (@mul_sig _ package).
  Local Notation carry_sig := (@carry_sig _ package).
  Local Notation sub_sig := (@sub_sig _ package).
  Local Notation square_sig := (@square_sig _ package).
  Local Notation tuple := Tuple.tuple.

  (** TODO(jadep,andreser): Move to NewBaseSystemTest? *)
  Definition FMxzladderstep := @M.donnaladderstep (F m) F.add F.sub F.mul.

  Section with_notations.
    Local Infix "+" := (proj1_sig add_sig).
    Local Notation "a * b" := (proj1_sig carry_sig (proj1_sig mul_sig a b)).
    Local Notation "x ^ 2" := (proj1_sig carry_sig (proj1_sig square_sig x)).
    Local Infix "-" := (proj1_sig sub_sig).
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

  (** TODO(jadep,andreser): Move to NewBaseSystemTest? *)
  Definition Mxzladderstep_sig
    : { xzladderstep : tuple Z sz -> tuple Z sz -> tuple Z sz * tuple Z sz -> tuple Z sz * tuple Z sz -> tuple Z sz * tuple Z sz * (tuple Z sz * tuple Z sz)
      | forall a24 x1 Q Q', let eval := B.Positional.Fdecode wt in Tuple.map (n:=2) (Tuple.map (n:=2) eval) (xzladderstep a24 x1 Q Q') = FMxzladderstep (eval a24) (eval x1) (Tuple.map (n:=2) eval Q) (Tuple.map (n:=2) eval Q') }.
  Proof.
    exists Mxzladderstep.
    intros a24 x1 Q Q' eval.
    cbv [Mxzladderstep FMxzladderstep M.donnaladderstep].
    destruct Q, Q'; cbv [Tuple.map Tuple.map' fst snd Let_In eval].
    repeat rewrite ?(proj2_sig add_sig), ?(proj2_sig mul_sig), ?(proj2_sig square_sig), ?(proj2_sig sub_sig), ?(proj2_sig carry_sig).
    reflexivity.
  Defined.
End with_package.

Ltac assert_xzladderstep_then package xzladderstep cont :=
  let feW' := fresh "feW'" in
  let phi' := fresh "phi'" in
  let a24_sig' := fresh "a24_sig'" in
  let FMxzladderstep' := fresh "FMxzladderstep'" in
  let wt' := fresh "wt'" in
  let feW_bounded := (eval_package_red_in package (@feW_bounded _ package)) in
  pose (@feW _ package) as feW';
  pose (@phiW _ package) as phi';
  pose (@a24_sig _ package) as a24_sig';
  pose (@FMxzladderstep package) as FMxzladderstep';
  pose (@wt _ package) as wt';
  assert (xzladderstep
          : { xzladderstep : feW' -> feW' * feW' -> feW' * feW' -> feW' * feW' * (feW' * feW')
            | forall x1 Q Q',
                let xz := xzladderstep x1 Q Q' in
                let eval := B.Positional.Fdecode wt' in
                feW_bounded x1
                -> feW_bounded (fst Q) /\ feW_bounded (snd Q)
                -> feW_bounded (fst Q') /\ feW_bounded (snd Q')
                -> ((feW_bounded (fst (fst xz)) /\ feW_bounded (snd (fst xz)))
                    /\ (feW_bounded (fst (snd xz)) /\ feW_bounded (snd (snd xz))))
                   /\ Tuple.map (n:=2) (Tuple.map (n:=2) phi') xz = FMxzladderstep' (eval (proj1_sig a24_sig')) (phi' x1) (Tuple.map (n:=2) phi' Q) (Tuple.map (n:=2) phi' Q') });
  [ cont feW' feW_bounded phi' a24_sig' FMxzladderstep' wt'
  | cbv delta [feW' feW_bounded phi' a24_sig' FMxzladderstep' wt'] in xzladderstep;
    clear feW' phi' a24_sig' FMxzladderstep' wt' ].

Ltac preglue_xzladderstep package feW' feW_bounded' phi' a24_sig' FMxzladderstep' wt' :=
  let Mxzladderstep_sig' := fresh "Mxzladderstep_sig'" in
  pose (@Mxzladderstep_sig package) as Mxzladderstep_sig';
  let a := fresh "a" in
  let b := fresh "b" in
  let c := fresh "c" in
  cbv [phiW] in phi';
  apply_lift_sig;
  intros a b c; cbv beta iota zeta;
  lazymatch goal with
  | [ |- { e | ?A -> ?B -> ?C -> @?E e } ]
    => refine (proj2_sig_map (P:=fun e => A -> B -> C -> (_:Prop)) _ _)
  end;
  [ let FINAL := fresh "FINAL" in
    intros ? FINAL;
    repeat (let H := fresh in intro H; specialize (FINAL H));
    cbv [phi'];
    split; [ refine (proj1 FINAL); shelve | ];
    do 4 match goal with
         | [ |- context[Tuple.map (n:=?N) (fun x : ?T => ?f (?g x))] ]
           => rewrite <- (Tuple.map_map (n:=N) f g
                          : pointwise_relation _ eq _ (Tuple.map (n:=N) (fun x : T => f (g x))))
         end;
    rewrite <- (proj2_sig Mxzladderstep_sig');
    apply f_equal;
    cbv [proj1_sig]; cbv [Mxzladderstep_sig' Mxzladderstep_sig];
    context_to_dlet_in_rhs (@Mxzladderstep _ _);
    hnf in a24_sig';
    cbv [Mxzladderstep a24_sig'];
    repeat lazymatch goal with
           | [ |- context[@proj1_sig ?a ?b ?f_sig _] ]
             => context_to_dlet_in_rhs (@proj1_sig a b f_sig)
           end;
    let mul_sig' := (eval_package_red_in package (@mul_sig _ package)) in
    let add_sig' := (eval_package_red_in package (@add_sig _ package)) in
    let sub_sig' := (eval_package_red_in package (@sub_sig _ package)) in
    let carry_sig' := (eval_package_red_in package (@carry_sig _ package)) in
    let square_sig' := (eval_package_red_in package (@square_sig _ package)) in
    cbv [sz ASParams ASPackage lgbitwidth package wt_gen
            proj1_sig
            mul_sig add_sig sub_sig carry_sig square_sig
            mul_sig' add_sig' sub_sig' carry_sig' square_sig'];
    cbv_runtime;
    refine (proj2 FINAL)
  | ];
  clear phi' a24_sig' FMxzladderstep' Mxzladderstep_sig' wt';
  let lgbitwidth' := (eval_package_red_in package (@lgbitwidth package)) in
  let sz' := (eval_package_red_in package (@sz package)) in
  cbv [feW' feW_bounded' feW feW_bounded
            ASParams ASPackage package lgbitwidth sz lgbitwidth' sz'] in *;
  clear feW'.

Ltac refine_reflectively_xzladderstep package :=
  let allowable_bit_widths := constr:(@allowable_bit_widths package) in
  refine_reflectively_gen allowable_bit_widths default.

Ltac pose_xzladderstep package xzladderstep :=
  assert_xzladderstep_then
    package xzladderstep
    ltac:(fun feW' feW_bounded' phi' a24_sig' FMxzladderstep' wt'
          => preglue_xzladderstep package feW' feW_bounded' phi' a24_sig' FMxzladderstep' wt';
             refine_reflectively_xzladderstep package).
