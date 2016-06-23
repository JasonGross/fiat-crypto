Require Export Crypto.Spec.WeierstrassCurve.

Require Import Crypto.Algebra.
Require Import Crypto.WeierstrassCurve.Pre Crypto.WeierstrassCurve.WeierstrassCurveDefinitions.
Require Import Coq.Logic.Eqdep_dec.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.

Module Extended.
  Section ExtendedCoordinates.
    Import Group Ring Field E.Notations E.PairNotations.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {a b : F}
            {field:@field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {prm:@E.weierstrass_params F Feq Fzero Fone Fopp Fadd Fmul a b}
            {eq_dec : DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "- x" := (Fopp x).
    Local Notation "x ^ 2" := (x*x). Local Notation "x ^ 3" := (x*x^2).
    Local Notation "'∞'" := unit : type_scope.
    Local Notation "'∞'" := (inr tt) : core_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Notation "2" := (1+1). Local Notation "3" := (1+2). Local Notation "4" := (1+3).
    Local Notation "8" := (1+(1+(1+(1+4)))). Local Notation "12" := (1+(1+(1+(1+8)))).
    Local Notation "16" := (1+(1+(1+(1+12)))). Local Notation "20" := (1+(1+(1+(1+16)))).
    Local Notation "24" := (1+(1+(1+(1+20)))). Local Notation "27" := (1+(1+(1+24))).
    Local Open Scope core_scope.
    Local Notation Epoint := (@E.point F Feq Fadd Fmul a b).
    Local Notation onCurve := (@Pre.onCurve F Feq Fadd Fmul a b).

    Add Field _weierstrass_curve_extended_field : (field_theory_for_stdlib_tactic (eq:=Feq)).
    Add Ring _weierstrass_curve_extended_ring : (ring_theory_for_stdlib_tactic (eq:=Feq)).

    (** [Extended.point] represents a point on an elliptic curve using
        homogenous projective coordinates (see
        <https://eprint.iacr.org/2015/1060.pdf>). *)

    Definition point := { P | let '(X,Y,Z) := P in Y^2*Z = X^3 + a*X*Z^2 + b*Z^3 /\ (X = 0 -> Y = 0 -> Z = 0 -> False) }.
    Definition coordinates (P:point) : F*F*F := proj1_sig P.

    Create HintDb bash discriminated.

    Local Hint Unfold fst snd sumwise fieldwise fieldwise' coordinates E.eq E.eq_coordinates E.coordinates proj1_sig Pre.onCurve : bash.
    Ltac bash' :=
      repeat match goal with
             | |- Proper _ _ => intro
             | _ => progress intros
             | [ H: _ /\ _ |- _ ] => destruct H
             | [ p:E.point |- _ ] => destruct p as [ [ [ ?? ] | ] ? ]
             | [ p:point |- _ ] => destruct p as [ [ [ ?? ] ? ] ?]
             | _ => progress destruct_trivial
             | _ => progress autounfold with bash in *
             | _ => progress break_match_when_head sumbool
             | _ => progress break_match_hyps_when_head sumbool
             | |- _ /\ _ => split
             | _ => solve [neq01]
             | _ => solve [eauto]
             | _ => solve [intuition]
             | _ => solve [etransitivity; eauto]
             | _ => solve [tauto]
             (*| |- Feq _ _ => field_algebra*)
             (*| |- _ <> 0 => apply mul_nonzero_nonzero*)
             | [ prm : E.weierstrass_params |- _ ] => destruct prm; try clear prm
             | _ => progress clear_algebraic_duplicates
             | [ H : _ <> 0 |- _ <> 0 ] =>
               intro; apply H;
               (*field_algebra;*)
               solve [ apply Ring.opp_nonzero_nonzero, E.char_gt_2
                     | apply E.char_gt_2]
             | _ => solve [ nsatz_contradict ]
             end.
    Ltac prebash_step :=
      match goal with
      | _ => solve [ trivial ]
      | [ |- ?R ?x ?x ] => reflexivity
      | [ H : False |- _ ] => exfalso; assumption
      | [ |- Proper _ _ ] => intro
      | _ => progress intros
      | [ H: _ /\ _ |- _ ] => destruct H
      | [ p:E.point |- _ ] => destruct p as [ [ [ ?? ] | ] ? ]
      | [ p:point |- _ ] => destruct p as [ [ [ ?? ] ? ] ?]
      | _ => progress destruct_trivial
      | _ => progress autounfold with bash in *
      | [ |- _ /\ _ ] => split
      | _ => progress break_innermost_match_step
      | [ H : context[match _ with _ => _ end] |- _ ] => revert H; progress break_innermost_match_step
      | [ H : 1 = 0 |- _ ] => solve [ exfalso; revert H; neq01 ]
      end.
    Ltac bash :=
      repeat match goal with
             | _ => prebash_step
             | _ => solve [ nsatz ]
             | _ => solve [ field_nsatz ]
             end.

    Local Obligation Tactic := bash.

    Program Definition to_homogenous (P:Epoint) : point := exist _
      (match P return _ with
       | ∞      => (0, 1, 0)
       | (x, y) => (x, y, 1)
       end) _.

    Program Definition from_homogenous (P:point) : Epoint := exist _
      (let '(X,Y,Z) := coordinates P in if dec (Z = 0) return _ then ∞ else ((X/Z), (Y/Z))) _.
    Definition eq (P Q:point) := E.eq (from_homogenous P) (from_homogenous Q).
    Global Instance DecidableRel_eq : Decidable.DecidableRel eq. exact _. Qed.

    Local Hint Unfold from_homogenous to_homogenous eq : bash.

    Global Instance Equivalence_eq : Equivalence eq. Proof. split; hnf; bash. Qed.
    Global Instance Proper_from_homogenous : Proper (eq==>E.eq) from_homogenous. Proof. bash. Qed.
    Global Instance Proper_to_homogenous : Proper (E.eq==>eq) to_homogenous. Proof. bash. Qed.
    Lemma from_to_homogenous P : E.eq (from_homogenous (to_homogenous P)) P. Proof. bash. Qed.

    Section aMinus3.
      Context {a_eq_minus3 : a = -(3)}.
      Context {nonzero_b : b <> 0}.
      Context {some_magic_I_dont_know_why : 8 * b^2 <> 27}.
      (*Context {twice_d:F} {Htwice_d:twice_d = d + d}.*)
      (** We require that there be an odd number of points on the
          curve.  Since every point [p] has a double [- p], and [-x =
          x -> x = 0] in the field, this is equivalent to requiring
          that [-p = p -> p = ∞], i.e., that (x, 0) is not on the
          curve *)
      Context {odd_elliptic_curve_order : forall x, x^3 + a*x + b <> 0}.
      (** Algorithm 4 from <https://eprint.iacr.org/2015/1060.pdf>, section 3.2 *)
      Definition add_coordinates P1 P2 : F*F*F :=
        let '(X1, Y1, Z1) := P1 in
        let '(X2, Y2, Z2) := P2 in
        let t0 := X1 * X2 in let t1 := Y1 * Y2 in let t2 := Z1 * Z2 in
        let t3 := X1 + Y1 in let t4 := X2 + Y2 in let t3 := t3 * t4 in
        let t4 := t0 + t1 in let t3 := t3 - t4 in let t4 := Y1 + Z1 in
        let X3 := Y2 + Z2 in let t4 := t4 * X3 in let X3 := t1 + t2 in
        let t4 := t4 - X3 in let X3 := X1 + Z1 in let Y3 := X2 + Z2 in
        let X3 := X3 * Y3 in let Y3 := t0 + t2 in let Y3 := X3 - Y3 in
        let Z3 := b * t2  in let X3 := Y3 - Z3 in let Z3 := X3 + X3 in
        let X3 := X3 + Z3 in let Z3 := t1 - X3 in let X3 := t1 + X3 in
        let Y3 := b * Y3  in let t1 := t2 + t2 in let t2 := t1 + t2 in
        let Y3 := Y3 - t2 in let Y3 := Y3 - t0 in let t1 := Y3 + Y3 in
        let Y3 := t1 + Y3 in let t1 := t0 + t0 in let t0 := t1 + t0 in
        let t0 := t0 - t2 in let t1 := t4 * Y3 in let t2 := t0 * Y3 in
        let Y3 := X3 * Z3 in let Y3 := Y3 + t2 in let X3 := t3 * X3 in
        let X3 := X3 - t1 in let Z3 := t4 * Z3 in let t1 := t3 * t0 in
        let Z3 := Z3 + t1 in
        (X3, Y3, Z3).

      Local Hint Unfold E.add E.coordinates add_coordinates : bash.

      Local Ltac bash_proper_step :=
        match goal with
        | _ => progress subst
        | _ => etransitivity; eassumption
        | _ => solve [ nsatz ]
        | _ => intro
        end.
      Local Ltac bash_proper := repeat bash_proper_step.
      Local Instance Proper_Feq_impl x : Proper (Feq ==> Basics.impl) (Feq x). Proof. bash_proper. Qed.
      Local Instance Proper_Feq_Feq_impl : Proper (Feq ==> Feq ==> Basics.impl) Feq. Proof. bash_proper. Qed.
      Local Instance Proper_Feq_flip_impl x : Proper (Feq ==> Basics.flip Basics.impl) (Feq x). Proof. bash_proper. Qed.
      Local Instance Proper_Feq_Feq_flip_impl : Proper (Feq ==> Feq ==> Basics.flip Basics.impl) Feq. Proof. bash_proper. Qed.
      Local Instance Proper_Feq_Feq_mul : Proper (Feq ==> Feq ==> Feq) Fmul := _.
      Local Instance Proper_Feq_mul x : Proper (Feq ==> Feq) (Fmul x) := _.
      Local Instance Proper_Feq_Feq_div : Proper (Feq ==> Feq ==> Feq) Fdiv := _.
      Local Instance Proper_Feq_div x : Proper (Feq ==> Feq) (Fdiv x) := _.
      Local Instance Proper_Feq_Feq_sub : Proper (Feq ==> Feq ==> Feq) Fsub := _.
      Local Instance Proper_Feq_sub x : Proper (Feq ==> Feq) (Fsub x) := _.
      Local Instance Proper_Feq_Feq_add : Proper (Feq ==> Feq ==> Feq) Fadd := _.
      Local Instance Proper_Feq_add x : Proper (Feq ==> Feq) (Fadd x) := _.
      Local Instance Proper_Feq_opp : Proper (Feq ==> Feq) Fopp := _.
      Local Instance Proper_Feq_inv : Proper (Feq ==> Feq) Finv := _.
      Local Instance Reflexive_Feq : Reflexive Feq := _.
      Local Instance Symmetric_Feq : Symmetric Feq := _.
      Local Instance Reflexive_flip_Feq : Reflexive (Basics.flip Feq) := _.
      Local Instance Proper_impl_not : Proper (Basics.impl ==> Basics.flip Basics.impl) not. Proof. firstorder. Qed.
      (* This next one doesn't do anything yet, but hopefully will soon;
       see bug #4776 There should be a way to terminate typeclass
       resolution early *)
      Hint Extern 0 (Proper (Basics.impl ==> Basics.impl) not) => fail : typeclass_instances.
      Hint Extern 0 (Proper (Basics.flip Basics.impl ==> Basics.flip Basics.impl) not) => fail : typeclass_instances.
      (*Global Instance Proper_add : Proper (eq==>eq==>eq) add. Proof. bash. Qed.
      Global Instance Proper_opp : Proper (eq==>eq) opp. Proof. bash. Qed.
      Global Instance Proper_coordinates : Proper (eq==>sumwise (fieldwise (n:=2) Feq) (fun _ _ => True)) coordinates. Proof. bash. Qed.*)

      Local Ltac destruct_points :=
        repeat match reverse goal with
               | [ p : point |- _ ]
                 => let X := fresh "X0" in
                    let Y := fresh "Y0" in
                    let Z := fresh "Z0" in
                    destruct p as [ [ [ X Y ] Z ] ? ]
               end.

      Lemma odd_elliptic_curve_order_useful (p : point)
        : let '(X, Y, Z) := coordinates p in Y <> 0.
      Proof.
        destruct p as [ [ [ X Y ] Z ] [ H0 H1 ] ]; simpl.
        destruct (dec (Z = 0)).
        { intro.
          apply H1; try assumption.
          nsatz. }
        { pose proof (odd_elliptic_curve_order (X/Z)).
          field_nsatz. }
      Qed.

      Local Ltac use_odd_order :=
        repeat match goal with
               | [ p : point |- _ ]
                 => unique pose proof (odd_elliptic_curve_order_useful p)
               end.

      Local Obligation Tactic := Program.Tactics.program_simpl.
      Program Definition add (P1 P2 : point) : point
        := exist _ (add_coordinates (coordinates P1) (coordinates P2)) _.
      Next Obligation.
      Proof.
        use_odd_order; destruct_points; destruct_head and; destruct prm.
        simpl in *.
        split.
        { clear f0 H2 odd_elliptic_curve_order.
          nsatz. }
        { intros.
          { repeat match goal with
                   | [ H : ?x <> 0, H' : _ = 0 -> _ |- _ ]
                     => match type of H' with
                        | x = 0 -> _ -> _ -> False => idtac
                        | _ -> x = 0 -> _ -> False => idtac
                        | _ -> _ -> x = 0 -> False => idtac
                        end;
                          clear H'
                   end.
            field_nsatz. (* does not solve the goal *)
            admit. } }
      Admitted.

      Local Notation eta3 v := (fst (fst v), snd (fst v), snd v) (only parsing).
      Lemma add_coordinates_correct' (P Q:point) :
        let '(X,Y,Z) := eta3 (add_coordinates (coordinates P) (coordinates Q)) in
        E.eq_coordinates
          (Feq := Feq)
          (E.coordinates (E.add (from_homogenous P) (from_homogenous Q)))
          (if dec (Z = 0) return _ then ∞ else ((X/Z), (Y/Z))).
      Proof.
        use_odd_order; destruct prm; clear prm.
        destruct_points; simpl in *; break_match_when_head sumbool;
          try solve [ simpl in *; trivial ].
        all:repeat match goal with
                   | [ |- ?R ?x ?x ] => reflexivity
                   | _ => progress destruct_head and
                   | _ => progress cbv [E.eq_coordinates sumwise fieldwise] in *
                   end.
        all:repeat match goal with
                   | [ H : ?x <> ?y, H' : ?x = ?y -> _ -> _ -> False |- _ ]
                     => clear H'
                   | [ H : ?x <> ?y, H' : _ -> ?x = ?y -> _ -> False |- _ ]
                     => clear H'
                   | [ H : ?x <> ?y, H' : _ -> _ -> ?x = ?y -> False |- _ ]
                     => clear H'
                   | [ H : _ -> _ -> ?T -> _, H' : ?T |- _ ]
                     => specialize (fun a b => H a b H')
                   end.
        all:[ > | | shelve | | shelve | | shelve.. ].
        par:abstract field_nsatz.
        Unshelve.
        { Time field_nsatz. admit. }
        { Time field_nsatz. }
        { Time field_nsatz. }
        { Time field_nsatz. }
        { Time field_nsatz. }
        { Time field_nsatz. }
      Admitted.

      Obligation Tactic := idtac.
      Program Definition add (P Q:point) : point := add_coordinates (coordinates P) (coordinates Q).
      Next Obligation.
        intros.
        pose proof (add_coordinates_correct P Q) as Hrep.
        pose proof Pre.unifiedAdd'_onCurve(a_nonzero:=E.nonzero_a)(a_square:=E.square_a)(d_nonsquare:=E.nonsquare_d)(char_gt_2:=E.char_gt_2) (E.coordinates (from_homogenous P)) (E.coordinates (from_homogenous Q)) as Hon.
        destruct P as [[[[]?]?][HP []]]; destruct Q as [[[[]?]?][HQ []]].
        pose proof weierstrassAddPlus (a_nonzero:=E.nonzero_a)(a_square:=E.square_a)(d_nonsquare:=E.nonsquare_d)(char_gt_2:=E.char_gt_2) _ _ _ _ HP HQ as Hnz1.
        pose proof weierstrassAddMinus (a_nonzero:=E.nonzero_a)(a_square:=E.square_a)(d_nonsquare:=E.nonsquare_d)(char_gt_2:=E.char_gt_2) _ _ _ _ HP HQ as Hnz2.
        autounfold with bash in *; simpl in *.
        destruct Hrep as [HA HB]. rewrite <-!HA, <-!HB; clear HA HB.
        bash.
      Qed.
      Local Hint Unfold add : bash.

      Lemma to_add P Q : E.eq (from_homogenous (add P Q)) (E.add (from_homogenous P) (from_homogenous Q)).
      Proof.
        pose proof (add_coordinates_correct P Q) as Hrep.
        destruct P as [[[[]?]?][HP []]]; destruct Q as [[[[]?]?][HQ []]].
        autounfold with bash in *; simpl in *.
        destruct Hrep as [HA HB]. rewrite <-!HA, <-!HB; clear HA HB.
        split; reflexivity.
      Qed.

      Global Instance Proper_add : Proper (eq==>eq==>eq) add.
      Proof.
        unfold eq. intros x y H x0 y0 H0.
        transitivity (from_homogenous x + from_homogenous x0)%E; rewrite to_add, ?H, ?H0; reflexivity.
      Qed.

      Lemma homomorphism_from_homogenous : @Group.is_homomorphism point eq add Epoint E.eq E.add from_homogenous.
      Proof. split; trivial using Proper_from_homogenous, to_add. Qed.

      Lemma add_from_twisted P Q : eq (from_twisted (P + Q)%E) (add (from_twisted P) (from_twisted Q)).
      Proof.
        pose proof (to_add (from_twisted P) (from_twisted Q)).
        unfold eq; rewrite !to_from_twisted in *.
        symmetry; assumption.
      Qed.

      Lemma homomorphism_from_twisted : @Group.is_homomorphism Epoint E.eq E.add point eq add from_twisted.
      Proof. split; trivial using Proper_from_twisted, add_from_twisted. Qed.

      Definition zero : point := from_twisted E.zero.
      Definition opp P : point := from_twisted (E.opp (from_homogenous P)).
      Lemma extended_group : @group point eq add zero opp.
      Proof.
        eapply @isomorphism_to_subgroup_group; eauto with typeclass_instances core.
        - apply DecidableRel_eq.
        - unfold opp. repeat intro. match goal with [H:_|-_] => rewrite H; reflexivity end.
        - intros. apply to_add.
        - unfold opp; intros; rewrite to_from_twisted; reflexivity.
        - unfold zero; intros; rewrite to_from_twisted; reflexivity.
      Qed.

      (* TODO: decide whether we still need those, then port *)
    (*
    Lemma unifiedAddM1_0_r : forall P, unifiedAddM1 P (mkExtendedPoint E.zero) === P.
      unfold equiv, extendedPoint_eq; intros.
      rewrite <-!unifiedAddM1_rep, unExtendedPoint_mkExtendedPoint, E.add_0_r; auto.
    Qed.

    Lemma unifiedAddM1_0_l : forall P, unifiedAddM1 (mkExtendedPoint E.zero) P === P.
      unfold equiv, extendedPoint_eq; intros.
      rewrite <-!unifiedAddM1_rep, E.add_comm, unExtendedPoint_mkExtendedPoint, E.add_0_r; auto.
    Qed.

    Lemma unifiedAddM1_assoc : forall a b c, unifiedAddM1 a (unifiedAddM1 b c) === unifiedAddM1 (unifiedAddM1 a b) c.
    Proof.
      unfold equiv, extendedPoint_eq; intros.
      rewrite <-!unifiedAddM1_rep, E.add_assoc; auto.
    Qed.

    Lemma testbit_conversion_identity : forall x i, N.testbit_nat x i = N.testbit_nat ((fun a => a) x) i.
    Proof.
      trivial.
    Qed.

    Lemma scalarMultM1_rep : forall n P, unExtendedPoint (nat_iter_op unifiedAddM1 (mkExtendedPoint E.zero) n P) = E.mul n (unExtendedPoint P).
      induction n; [simpl; rewrite !unExtendedPoint_mkExtendedPoint; reflexivity|]; intros.
      unfold E.mul; fold E.mul.
      rewrite <-IHn, unifiedAddM1_rep; auto.
    Qed.
     *)
    End TwistMinus1.
  End ExtendedCoordinates.

  Section Homomorphism.
    Import Group Ring Field.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv Fa Fd}
            {fieldF:@field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {Fprm:@E.weierstrass_params F Feq Fzero Fone Fadd Fmul Fa Fd}.
    Context {K Keq Kzero Kone Kopp Kadd Ksub Kmul Kinv Kdiv Ka Kd}
            {fieldK:@field K Keq Kzero Kone Kopp Kadd Ksub Kmul Kinv Kdiv}
            {Kprm:@E.weierstrass_params K Keq Kzero Kone Kadd Kmul Ka Kd}.
    Context {phi:F->K} {Hphi:@Ring.is_homomorphism F Feq Fone Fadd Fmul
                                                   K Keq Kone Kadd Kmul phi}.
    Context {phi_nonzero : forall x, ~ Feq x Fzero -> ~ Keq (phi x) Kzero}.
    Context {HFa: Feq Fa (Fopp Fone)} {HKa:Keq Ka (Kopp Kone)}.
    Context {Hd:Keq (phi Fd) Kd} {Kdd Fdd} {HKdd:Keq Kdd (Kadd Kd Kd)} {HFdd:Feq Fdd (Fadd Fd Fd)}.
    Local Notation Fpoint := (@point F Feq Fzero Fone Fadd Fmul Fdiv Fa Fd).
    Local Notation Kpoint := (@point K Keq Kzero Kone Kadd Kmul Kdiv Ka Kd).

    Lemma Ha : Keq (phi Fa) Ka.
    Proof. rewrite HFa, HKa, <-homomorphism_one. eapply homomorphism_opp. Qed.

    Lemma Hdd : Keq (phi Fdd) Kdd.
    Proof. rewrite HFdd, HKdd. rewrite homomorphism_add. repeat f_equiv; auto. Qed.

    Create HintDb field_homomorphism discriminated.
    Hint Rewrite <-
         homomorphism_one
         homomorphism_add
         homomorphism_sub
         homomorphism_mul
         homomorphism_div
         Ha
         Hd
         Hdd
      : field_homomorphism.

    Program Definition ref_phi (P:Fpoint) : Kpoint := exist _ (
      let '(X, Y, Z, T) := coordinates P in (phi X, phi Y, phi Z, phi T)) _.
    Next Obligation.
      destruct P as [[[[] ?] ?] [? [? ?]]]; unfold onCurve in *; simpl.
      rewrite_strat bottomup hints field_homomorphism.
      eauto 10 using is_homomorphism_phi_proper, phi_nonzero.
    Qed.

    Context {point_phi:Fpoint->Kpoint}
            {point_phi_Proper:Proper (eq==>eq) point_phi}
            {point_phi_correct: forall (P:Fpoint), eq (point_phi P) (ref_phi P)}.

    Lemma lift_homomorphism : @Group.is_homomorphism Fpoint eq (add(a_eq_minus1:=HFa)(Htwice_d:=HFdd)) Kpoint eq (add(a_eq_minus1:=HKa)(Htwice_d:=HKdd)) point_phi.
    Proof.
      repeat match goal with
             | |- Group.is_homomorphism => split
             | |- _ => intro
             | |-  _ /\ _ => split
             | [H: _ /\ _ |- _ ] => destruct H
             | [p: point |- _ ] => destruct p as [[[[] ?] ?] [? [? ?]]]
             | |- context[point_phi] => setoid_rewrite point_phi_correct
             | |- _ => progress cbv [fst snd coordinates proj1_sig eq from_homogenous E.eq_coordinates E.eq E.coordinates fieldwise fieldwise' add add_coordinates ref_phi] in *
             | |- Keq ?x ?x => reflexivity
             | |- Keq ?x ?y => rewrite_strat bottomup hints field_homomorphism
             | [ H : Feq _ _ |- Keq (phi _) (phi _)] => solve [f_equiv; intuition]
             end.
    Qed.
  End Homomorphism.
End Extended.
