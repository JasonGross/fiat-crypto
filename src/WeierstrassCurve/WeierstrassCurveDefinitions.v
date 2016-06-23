Require Export Crypto.Spec.WeierstrassCurve.

Require Import Crypto.Algebra.
Require Import Crypto.WeierstrassCurve.Pre.
Require Import Coq.Logic.Eqdep_dec.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import Crypto.Util.Tuple Crypto.Util.Sum Crypto.Util.Unit.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Notations.

Module E.
  Import Group Ring Field WeierstrassCurve.E.
  Module Export Notations.
    Notation "'∞'" := unit : type_scope.
    Notation "'∞'" := (inr tt) : core_scope.
  End Notations.
  Module Import PairNotations.
    Notation "( x , y )" := (inl (pair x y)).
  End PairNotations.

  Section WeierstrassCurveTheorems.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {a b : F}
            {field:@field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {prm:@weierstrass_params F Feq Fzero Fone Fopp Fadd Fmul a b}
            {eq_dec : DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "- x" := (Fopp x).
    Local Notation "x ^ 2" := (x*x). Local Notation "x ^ 3" := (x*x^2).
    Local Notation "'∞'" := unit : type_scope.
    Local Notation "'∞'" := (inr tt) : core_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Notation "2" := (1+1). Notation "3" := (1+2).
    Local Open Scope core_scope.

    Local Notation point := (@point F Feq Fadd Fmul a b).
    Local Notation onCurve := (@onCurve F Feq Fadd Fmul a b).

    Add Field _weierstrass_curve_theorems_field : (field_theory_for_stdlib_tactic (eq := Feq)).
    Add Ring _weierstrass_curve_theorems_ring : (ring_theory_for_stdlib_tactic (eq := Feq)).

    Definition eq_coordinates (P Q:F*F + ∞) := sumwise (fieldwise (n:=2) Feq) (fun _ _ => True) P Q.
    Definition eq (P Q:point) := eq_coordinates (coordinates P) (coordinates Q).
    Local Infix "=" := eq : E_scope.
    Global Instance DecidableRel_eq : DecidableRel eq. exact _. Qed.

    Local Ltac destruct_points :=
      repeat match goal with
             | [ p : point |- _ ] =>
               let x := fresh "x" p in
               let y := fresh "y" p in
               let pf := fresh "pf" p in
               destruct p as [ [ [x y] | [ ] ] pf]
             end.

    Local Obligation Tactic := intros; destruct_points; simpl; trivial; try nsatz.
    Program Definition opp (P:point) : point :=
      exist _ (match coordinates P with
               | (x, y) => (x, Fopp y)
               | ∞      => ∞
               end) _.

    (*Section PointCompression.
      Local Notation "x ^ 2" := (x*x).
      Definition solve_for_x2 (y : F) := ((y^2 - 1) / (d * (y^2) - a)).

      Lemma a_d_y2_nonzero : forall y, d * y^2 - a <> 0.
      Proof.
        intros ? eq_zero.
        destruct square_a as [sqrt_a sqrt_a_id]; rewrite <- sqrt_a_id in eq_zero.
        destruct (eq_dec y 0); [apply nonzero_a|apply nonsquare_d with (sqrt_a/y)]; field_algebra.
      Qed.

      Lemma solve_correct : forall x y, onCurve (x, y) <-> (x^2 = solve_for_x2 y).
      Proof.
        unfold solve_for_x2; simpl; split; intros; field_algebra; auto using a_d_y2_nonzero.
      Qed.
    End PointCompression.*)
  End WeierstrassCurveTheorems.
(*
  Section Homomorphism.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv Fa Fb}
            {fieldF:@field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {Fprm:@weierstrass_params F Feq Fzero Fone Fopp Fadd Fmul Fa Fb}.
    Context {K Keq Kzero Kone Kopp Kadd Ksub Kmul Kinv Kdiv Ka Kb}
            {fieldK:@field K Keq Kzero Kone Kopp Kadd Ksub Kmul Kinv Kdiv}
            {Kprm:@weierstrass_params K Keq Kzero Kone Kopp Kadd Kmul Ka Kb}.
    Context {phi:F->K} {Hphi:@Ring.is_homomorphism F Feq Fone Fadd Fmul
                                                   K Keq Kone Kadd Kmul phi}.
    Context {Ha:Keq (phi Fa) Ka} {Hd:Keq (phi Fb) Kb}.
    Local Notation Fpoint := (@point F Feq Fadd Fmul Fa Fb).
    Local Notation Kpoint := (@point K Keq Kadd Kmul Ka Kb).
    Local Open Scope core_scope.

    Create HintDb field_homomorphism discriminated.
    Hint Rewrite <-
         homomorphism_one
         homomorphism_add
         homomorphism_sub
         homomorphism_mul
         homomorphism_div
         Ha
         Hd
      : field_homomorphism.

    Program Definition ref_phi (P:Fpoint) : Kpoint := exist _ (
      match coordinates P return _ with
      | (x, y) => (phi x, phi y)
      | ∞ => ∞
      end) _.
    Next Obligation.
      destruct P as [[[? ?]|] ?]; simpl; destruct_trivial; trivial.
      rewrite_strat bottomup hints field_homomorphism.
      eauto using is_homomorphism_phi_proper; assumption.
    Qed.

    Context {point_phi:Fpoint->Kpoint}
            {point_phi_Proper:Proper (eq==>eq) point_phi}
            {point_phi_correct: forall (P:Fpoint), eq (point_phi P) (ref_phi P)}.

    Lemma lift_homomorphism : @Group.is_homomorphism Fpoint eq add Kpoint eq add point_phi.
    Proof.
      repeat match goal with
             | |- Group.is_homomorphism => split
             | |- _ => intro
             | |-  _ /\ _ => split
             | [H: _ /\ _ |- _ ] => destruct H
             | [p: point |- _ ] => destruct p as [[[??]|]?]
             | |- context[point_phi] => setoid_rewrite point_phi_correct
             | |- _ => progress cbv [fst snd coordinates proj1_sig eq sumwise fieldwise fieldwise' add zero opp ref_phi ref_phi proj2_sig] in *
             | |- Keq ?x ?x => reflexivity
             | |- Keq ?x ?y => rewrite_strat bottomup hints field_homomorphism
             | [ H : Feq _ _ |- Keq (phi _) (phi _)] => solve [f_equiv; intuition]
             end.
      repeat match goal with
             | _ => progress break_match_when_head @sumbool
             | _ => progress break_match_when_head @sum
             | [ H : _ = left _ :> sumbool _ _ |- _ ] => clear H
             | [ H : _ = right _ :> sumbool _ _ |- _ ] => clear H
             | [ H : match ?e with _ => _ end = _ :> sum _ _ |- _ ] => destruct e eqn:?
             | _ => progress subst
             | _ => progress congruence_sum
             end.
{       repeat match goal with
             | |- Group.is_homomorphism => split
             | |- _ => intro
             | |-  _ /\ _ => split
             | [H: _ /\ _ |- _ ] => destruct H
             | [p: point |- _ ] => destruct p as [[[??]|]?]
             | |- context[point_phi] => setoid_rewrite point_phi_correct
             | |- _ => progress cbv [fst snd coordinates proj1_sig eq sumwise fieldwise fieldwise' add zero opp ref_phi ref_phi proj2_sig] in *
             | |- Keq ?x ?x => reflexivity
             | |- Keq ?x ?y => rewrite_strat bottomup hints field_homomorphism
             | [ H : Feq _ _ |- Keq (phi _) (phi _)] => solve [f_equiv; intuition]
             end.
move p0 at bottom.
destruct p0.
{ repeat match goal with
             | |- Group.is_homomorphism => split
             | |- _ => intro
             | |-  _ /\ _ => split
             | [H: _ /\ _ |- _ ] => destruct H
             | [p: point |- _ ] => destruct p as [[[??]|]?]
             | |- context[point_phi] => setoid_rewrite point_phi_correct
             | |- _ => progress cbv [fst snd coordinates proj1_sig eq sumwise fieldwise fieldwise' add zero opp ref_phi ref_phi proj2_sig] in *
             | |- Keq ?x ?x => reflexivity
             | |- Keq ?x ?y => rewrite_strat bottomup hints field_homomorphism
             | [ H : Feq _ _ |- Keq (phi _) (phi _)] => solve [f_equiv; intuition]
             end.
    Qed.
  End Homomorphism.*)
End E.

Export E.Notations.
