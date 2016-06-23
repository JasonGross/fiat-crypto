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
Require Import Crypto.WeierstrassCurve.WeierstrassCurveDefinitions.

Module E.
  Import Group Ring Field WeierstrassCurve.E WeierstrassCurveDefinitions.E.
  Import PairNotations.
  Section WeierstrassCurveTheorems.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {a b : F}
            {field:@field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {prm:@weierstrass_params F Feq Fzero Fone Fopp Fadd Fmul a b}
            {eq_dec : DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "x =? y" := (dec (x = y)) : type_scope.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "- x" := (Fopp x).
    Local Notation "x ^ 2" := (x*x). Local Notation "x ^ 3" := (x*x^2).
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Notation "2" := (1+1). Notation "3" := (1+2).
    Local Open Scope core_scope.
    Local Notation eq := (@E.eq F Feq Fadd Fmul a b).

    Local Notation point := (@point F Feq Fadd Fmul a b).
    Local Notation onCurve := (@onCurve F Feq Fadd Fmul a b).

    Add Field _weierstrass_curve_theorems_field : (field_theory_for_stdlib_tactic (eq := Feq)).
    Add Ring _weierstrass_curve_theorems_ring : (ring_theory_for_stdlib_tactic (eq := Feq)).

    Ltac destruct_points :=
      repeat match goal with
             | [ p : point |- _ ] =>
               let x := fresh "x" p in
               let y := fresh "y" p in
               let pf := fresh "pf" p in
               destruct p as [ [ [ x y ] | [ ] ] pf]
             end.

    Ltac expand_opp :=
      rewrite ?mul_opp_r, ?mul_opp_l, ?ring_sub_definition, ?inv_inv, <-?ring_sub_definition.

    Local Hint Resolve char_gt_2.
    (*Local Hint Resolve nonzero_a.
    Local Hint Resolve square_a.
    Local Hint Resolve nonsquare_d.*)
    (*Local Hint Resolve @weierstrassAddPlus.
    Local Hint Resolve @weierstrassAddMinus.*)

    Local Obligation Tactic := intros; destruct_points; simpl; trivial; try nsatz.

    Local Ltac neq_inv_to_neq R opp :=
      match goal with
      | [ H : ~R ?x (opp ?y) |- _ ]
        => not constr_eq x y;
           match goal with
           | [ H' : ~R x y |- _ ] => fail 1
           | [ H' : R x y |- _ ] => fail 1
           | _ => idtac
           end;
           destruct (dec (R x y))
      | [ H : ~R (opp ?x) ?y |- _ ]
        => not constr_eq x y;
           match goal with
           | [ H' : ~R x y |- _ ] => fail 1
           | [ H' : R x y |- _ ] => fail 1
           | _ => idtac
           end;
           destruct (dec (R x y))
      end.

    Local Ltac bash_step :=
      match goal with
      | |- _ => progress intros
      | [H: _ /\ _ |- _ ] => destruct H
      | _ => tauto
      | [ H : ?x <> ?x |- _ ] => specialize (H (reflexivity _))
      | [ H : Feq ?x ?x |- _ ] => clear H
      | [ |- ?R ?x ?x ] => reflexivity
      | [ H : Feq ?x ?x |- _ ] => clear H
      | |- _ => progress destruct_points
      | |- _ => progress cbv [add fst snd coordinates proj1_sig eq eq_coordinates fieldwise fieldwise' sumwise add zero opp] in *
      | |- _ => split
      (*| |- Feq _ _ => field_algebra*)
      (*| |- _ <> 0 => expand_opp; solve [nsatz_nonzero|eauto 6]*)
      | _ => progress break_match
      | _ => intro
      | _ => progress setoid_subst_rel Feq
      | _ => neq_inv_to_neq Feq Fopp
      | _ => solve [ exfalso; eauto using only_two_square_roots ]
      | [ |- False ] => solve [ nsatz_contradict ]
      | [ |- Decidable _ ] => solve [ typeclasses eauto ]
      | [ H : ?x <> -?x |- _ ]
        => unique assert (x <> 0); [ solve [ nsatz_contradict ] | ]
      | _ => progress clear_duplicates
      | _ => progress field_nonzero_mul_split
      | _ => progress canonicalize_field_inequalities
      (*| |- {_}+{_} => eauto 15 using decide_and, @eq_dec with typeclass_instances*)
      end.

    Ltac bash := repeat bash_step.
    Ltac slow_bash
      := repeat first [ progress bash_step
                      | match goal with
                        | [ |- Feq _ _ ] => solve [ field_nsatz ]
                        end ].
    Global Instance Equivalence_eq : Equivalence eq. Proof. bash. Qed.
    Local Instance Proper_Feq_impl x : Proper (Feq ==> Basics.impl) (Feq x). Proof. bash. Qed.
    Local Instance Proper_Feq_Feq_impl : Proper (Feq ==> Feq ==> Basics.impl) Feq. Proof. bash. Qed.
    Local Instance Proper_Feq_flip_impl x : Proper (Feq ==> Basics.flip Basics.impl) (Feq x). Proof. bash. Qed.
    Local Instance Proper_Feq_Feq_flip_impl : Proper (Feq ==> Feq ==> Basics.flip Basics.impl) Feq. Proof. bash. Qed.
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
    Global Instance Proper_add : Proper (eq==>eq==>eq) add. Proof. bash. Qed.
    Global Instance Proper_opp : Proper (eq==>eq) opp. Proof. bash. Qed.
    Global Instance Proper_coordinates : Proper (eq==>sumwise (fieldwise (n:=2) Feq) (fun _ _ => True)) coordinates. Proof. bash. Qed.

    Local Ltac easy_fin :=
      solve [ trivial
            | match goal with
              | [ |- ?R ?x ?x ] => reflexivity
              | [ H : False |- _ ] => destruct H; easy_fin
              | [ H : not (?R ?x ?x) |- _ ] => specialize (H (reflexivity _)); easy_fin
              | [ H : ~?T, H' : ?T |- _ ] => specialize (H H'); easy_fin
              end ].
    Local Ltac hard_fin :=
      solve [ only_two_square_roots ].
    Local Ltac pre_t_step :=
      first [ easy_fin
            | intro
            | progress cbv [add fst snd coordinates proj1_sig eq eq_coordinates fieldwise fieldwise' sumwise add zero opp] in *
            | progress destruct_head and
            | progress destruct_points
            | progress break_match_when_head sumbool
            | progress repeat neq_inv_to_neq Feq Fopp
            | progress setoid_subst_rel Feq
            | apply conj
            | hard_fin ].
    Local Ltac pre_t := repeat pre_t_step; clear_algebraic_duplicates.

    Global Instance weierstrass_acurve_abelian_group : abelian_group (eq:=eq)(op:=add)(id:=zero)(inv:=opp).
    Proof.
      (*destruct prm; clear prm; split.
      Set Ltac Profiling.
      Focus 2.
      { Reset Ltac Profile.
        constructor; pre_t.
        Show Ltac Profile.
        Time par: abstract super_nsatz. }
      Unfocus.
      split; [ split.. | ]; try exact _;
        [ split.. | | ].
      5: solve [ pre_t; super_nsatz ].
      4: solve [ pre_t; super_nsatz ].
      3: solve [ pre_t; super_nsatz ].
      2: solve [ pre_t; super_nsatz ].
      { Set Ltac Profiling.
        intros;
          repeat first [ easy_fin
                       | progress cbv [add fst snd coordinates proj1_sig eq eq_coordinates fieldwise fieldwise' sumwise add zero opp] in *
                       | progress destruct_head and
                       | progress destruct_points
                       | progress break_match_when_head sumbool
                       | apply conj ].
        { Time pre_t; super_nsatz. }
        { Time pre_t; super_nsatz. }
        { Time pre_t; super_nsatz. }
        { setoid_subst_rel Feq.
          shelve. }
        { setoid_subst_rel Feq.
          shelve. }
        { setoid_subst_rel Feq.
          shelve. }
        { Time pre_t.
          conservative_common_denominator_equality_inequality_all.
          super_nsatz.
          { nsatz_contradict. }
          { nsatz_contradict. }
          { conservative_common_denominator_equality_inequality_all; [ | nsatz_contradict ].
            field_simplify_eq_all.
            super_nsatz. } }
        { super_nsatz. }
            intro; apply n0.
            clear nonzero_discriminant0.
            clear n.
            clear char_gt_3 char_ne_4.
            clear n0.
Require Import Coq.Reals.Reals Coq.nsatz.Nsatz.

Local Open Scope R.

Goal forall a b yx xz : R,
  yx^2 = xz^3 + a * xz + b ->
  (- yx)^2 = xz^3 + a * xz + b ->
  xz * (2 * yx)^2 - ((3 * xz^2 + a)^2 - xz * (2 * yx)^2 - xz * (2 * yx)^2) = 0 ->
  (3 * xz^2 + a)^2 - 2 * (2 * yx)^2 * xz = (2 * yx)^2 * xz.
Proof.
  intros ???? H0 H1 H2.
  nsatz.

            nsatz.
            revert a b yx xz pfx pfz H.
            field_simplify_eq_all.
            nsatz.
            super_nsatz. } }
        {
          {
            nsatz_contradict.
          { nsatz_contradict. }
            { super_nsatz. }
            { nsatz_contradict. } }
          { nsatz_contradict.
clear n0.
            split_field_inequalities.
            { super_nsatz. }
 }
        { nsatz. }
        setoid_subst_rel Feq.
            | progress repeat neq_inv_to_neq Feq Fopp ].
        Reset Ltac Profile.
Focus 64.
setoid_subst_rel Feq.
Show Ltac Profile.
first [ easy_fin
            | intro
            | progress cbv [add fst snd coordinates proj1_sig eq eq_coordinates fieldwise fieldwise' sumwise add zero opp] in *
            | progress destruct_head and
            | progress destruct_points
            | progress break_match_when_head sumbool
            | progress repeat neq_inv_to_neq Feq Fopp ].
        Timeout 2 64: pre_t_step.
Timeout 2 63: pre_t_step.
Timeout 2 62: pre_t_step.
Timeout 2 61: pre_t_step.
Timeout 2 60: pre_t_step.
Timeout 2 59: pre_t_step.
Timeout 2 58: pre_t_step.
Timeout 2 57: pre_t_step.
Timeout 2 56: pre_t_step.
Timeout 2 55: pre_t_step.
Timeout 2 54: pre_t_step.
Timeout 2 53: pre_t_step.
Timeout 2 52: pre_t_step.
Timeout 2 51: pre_t_step.
Timeout 2 50: pre_t_step.
Timeout 2 49: pre_t_step.
Timeout 2 48: pre_t_step.
Timeout 2 47: pre_t_step.
Timeout 2 46: pre_t_step.
Timeout 2 45: pre_t_step.
Timeout 2 44: pre_t_step.
Timeout 2 43: pre_t_step.
Timeout 2 42: pre_t_step.
Timeout 2 41: pre_t_step.
Timeout 2 40: pre_t_step.
Timeout 2 39: pre_t_step.
Timeout 2 38: pre_t_step.
Timeout 2 37: pre_t_step.
Timeout 2 36: pre_t_step.
Timeout 2 35: pre_t_step.
Timeout 2 34: pre_t_step.
Timeout 2 33: pre_t_step.
Timeout 2 32: pre_t_step.
Timeout 2 31: pre_t_step.
Timeout 2 30: pre_t_step.
Timeout 2 29: pre_t_step.
Timeout 2 28: pre_t_step.
Timeout 2 27: pre_t_step.
Timeout 2 26: pre_t_step.
Timeout 2 25: pre_t_step.
Timeout 2 24: pre_t_step.
Timeout 2 23: pre_t_step.
Timeout 2 22: pre_t_step.
Timeout 2 21: pre_t_step.
Timeout 2 20: pre_t_step.
Timeout 2 19: pre_t_step.
Timeout 2 18: pre_t_step.
Timeout 2 17: pre_t_step.
Timeout 2 16: pre_t_step.
Timeout 2 15: pre_t_step.
Timeout 2 14: pre_t_step.
Timeout 2 13: pre_t_step.
Timeout 2 12: pre_t_step.
Timeout 2 11: pre_t_step.
Timeout 2 10: pre_t_step.
Timeout 2 9: pre_t_step.
Timeout 2 8: pre_t_step.
Timeout 2 7: pre_t_step.
Timeout 2 6: pre_t_step.
Timeout 2 5: pre_t_step.
Timeout 2 4: pre_t_step.
Timeout 2 3: pre_t_step.
Timeout 2 2: pre_t_step.
Timeout 2 1: pre_t_step.

        all: pre_t_step.

        all: pre_t_step.
        all: pre_t_step.
        Timeout 2 64: pre_t_step.
Timeout 2 63: pre_t_step.
Timeout 2 62: pre_t_step.
Timeout 2 61: pre_t_step.
Timeout 2 60: pre_t_step.
Timeout 2 59: pre_t_step.
Timeout 2 58: pre_t_step.
Timeout 2 57: pre_t_step.
Timeout 2 56: pre_t_step.
Timeout 2 55: pre_t_step.
Timeout 2 54: pre_t_step.
Timeout 2 53: pre_t_step.
Timeout 2 52: pre_t_step.
Timeout 2 51: pre_t_step.
Timeout 2 50: pre_t_step.
Timeout 2 49: pre_t_step.
Timeout 2 48: pre_t_step.
Timeout 2 47: pre_t_step.
Timeout 2 46: pre_t_step.
Timeout 2 45: pre_t_step.
Timeout 2 44: pre_t_step.
Timeout 2 43: pre_t_step.
Timeout 2 42: pre_t_step.
Timeout 2 41: pre_t_step.
Timeout 2 40: pre_t_step.
Timeout 2 39: pre_t_step.
Timeout 2 38: pre_t_step.
Timeout 2 37: pre_t_step.
Timeout 2 36: pre_t_step.
Timeout 2 35: pre_t_step.
Timeout 2 34: pre_t_step.
Timeout 2 33: pre_t_step.
Timeout 2 32: pre_t_step.
Timeout 2 31: pre_t_step.
Timeout 2 30: pre_t_step.
Timeout 2 29: pre_t_step.
Timeout 2 28: pre_t_step.
Timeout 2 27: pre_t_step.
Timeout 2 26: pre_t_step.
Timeout 2 25: pre_t_step.
Timeout 2 24: pre_t_step.
Timeout 2 23: pre_t_step.
Timeout 2 22: pre_t_step.
Timeout 2 21: pre_t_step.
Timeout 2 20: pre_t_step.
Timeout 2 19: pre_t_step.
Timeout 2 18: pre_t_step.
Timeout 2 17: pre_t_step.
Timeout 2 16: pre_t_step.
Timeout 2 15: pre_t_step.
Timeout 2 14: pre_t_step.
Timeout 2 13: pre_t_step.
Timeout 2 12: pre_t_step.
Timeout 2 11: pre_t_step.
Timeout 2 10: pre_t_step.
Timeout 2 9: pre_t_step.
Timeout 2 8: pre_t_step.
Timeout 2 7: pre_t_step.
Timeout 2 6: pre_t_step.
Timeout 2 5: pre_t_step.
Timeout 2 4: pre_t_step.
Timeout 2 3: pre_t_step.
Timeout 2 2: pre_t_step.
Timeout 2 1: pre_t_step.
        64: pre_t_step.
        63: pre_t_step.
        62: pre_t_step.
        61: pre_t_step.
        60: pre_t_step.
        59: pre_t_step.

        pre_t_step.
        pre_t_step.
        pre_t_step.
        pre_t_step.
        pre_t_step.
        pre_t_step.
        pre_t_step.
        { super_nsatz. }
        pre_t_step.
        pre_t_step.
        pre_t_step.
        { super_nsatz
        pre_t_step.

      1:solve [ constructor; pre_t; super_nsatz ].
      4:solve [ bash ].
      3:solve [ bash ].
      2:solve [ bash ].
      2:solve [ bash ].
      { split.
        intros.
        unfold add.
        progress cbv [add fst snd coordinates proj1_sig eq fieldwise fieldwise' sumwise add zero opp] in *.
        destruct_points.
        8:solve [ bash ].
        7:solve [ bash ].
        6:solve [ bash ].
        4:solve [ bash ].
        all:repeat break_match_when_head_step sumbool; trivial.
        1:solve [ slow_bash ].
        Set Ltac Profiling.
        { bash.
          clear_duplicates.
          conservative_common_denominator_all.
          clear_duplicates.
          field_nonzero_mul_split.
          clear_duplicates.
          nsatz_contradict. }
        all:bash.
        all:clear_duplicates.
        all:conservative_common_denominator_all.
        all:clear_duplicates.
        all:field_nonzero_mul_split.
        all:clear_duplicates.
        all:nsatz_contradict.
          { bash.
            { clear_duplicates.
              conservative_common_denominator_all.
              clear_duplicates.
            field_nonzero_mul_split.
            clear_duplicates.
            nsatz_contradict. }
            field_nonzero_mul_split.
              assumption.
              assumption.
              assumption.
              assumption.

              unfold Algebra_syntax.equality.
              unfold Algebra_syntax.zero.
              unfold Ncring.eq_notation.
              unfold Ncring.zero_notation.
              intro; apply char_ne_4.
              nsatz. }
            { bash.

nsatz.
              nsatz_contradict.
              assumption.


              repeat match goal with
                     | [ H : _ |- _ ] => rewrite IntegralDomain.mul_nonzero_nonzero_iff in H; destruct H
                     | [ H : ?T, H' : ?T |- _ ] => clear H'
                     end.
              nsatz_contradict.
              unfold Algebra_syntax.equality.
              unfold Algebra_syntax.zero.
              unfold Ncring.eq_notation.
              unfold Ncring.zero_notation.
              field_nonzero_mul_split.
              nsatz.

              nsatz_contradict. }
              conservative_common_denominator_in pfz.

Ltac set_nonfraction_pieces_in_by H nonzero_tac ::=
  idtac;
  let fld := guess_field in
  lazymatch type of fld with
  | @Algebra.field ?T ?eq ?zero ?one ?opp ?add ?sub ?mul ?inv ?div
    => let T := type of H in
       set_nonfraction_pieces_on
         T eq zero opp add sub mul inv div nonzero_tac
         ltac:(fun T' => change T' in H)
  end.


Ltac deduplicate_nonfraction_pieces mul :=
  repeat match goal with
         | [ x0 := ?v, x1 := context[?v] |- _ ]
             => progress change v with x0 in x1
         | [ x := mul ?a ?b |- _ ]
           => not is_var a;
              let a' := fresh x in
              pose a as a'; change a with a' in x
         | [ x := mul ?a ?b |- _ ]
           => not is_var b;
              let b' := fresh x in
              pose b as b'; change b with b' in x
         | [ x0 := ?v, x1 := ?v |- _ ]
           => change x1 with x0 in *; clear x1
         | [ x := ?v |- _ ]
           => is_var v; subst x
         | [ x0 := mul ?a ?b, x1 := mul ?a ?b' |- _ ]
           => subst x0 x1
         | [ x0 := mul ?a ?b, x1 := mul ?a' ?b |- _ ]
           => subst x0 x1
         end.
deduplicate_nonfraction_pieces Fmul.



Require Import Coq.setoid_ring.Field_tac.
field_simplify_eq in pfz.
split; intro; tauto.
              revert pfz.

              Print Ltac common_denominator_in.
Require Import Coq.Classes.Morphisms. Require Coq.Setoids.Setoid.
Require Import Crypto.Util.Tactics Crypto.Tactics.Nsatz.
Require Import Crypto.Util.Decidable.

              field_simplify_eq in pfz.
split_nonfraction_pieces Fmul.
conservative_common_denominator_all.
              match goal with [H: _ |- _ _ _ ] => progress conservative_common_denominator_in H; [] end.
conservative_common_denominator_in f2.

            nsatz_contradict.
            Foc

            assert (yx <> 0) by nsatz_contradict.
            assert ((3 * xz^2 + a)^2 = (2 * yx)^2 * (3 * xz)).
            clear f0 pfz pfx pfy.
            clear n.
            destruct prm.
            assert ((3 * xz^2 + a)^2 / (2 * yx)^2 = 3 * xz).
            nsatz.
            clear f2.
            rewrite <- H0.
            clear H0.
            field_algebra.
            clear f2.
            rewrite f0 in pfz.

            clear pfz pfy.
            rewrite H0 in f0.
            destruct prm.
            apply n.
            Print Algebra.field.
            nsatz.
              match

                        let H := constr:(f0) in
            let div := constr:(Fdiv) in
            let eq := constr:(Feq) in
            let zero := constr:(0) in
            let nonzero_tac := intro; field_nonzero_mul_split; tauto in
            repeat match type of H with
                   | context[div ?x ?y]
                     => not is_var y;
                          let y' := fresh "y" in
                          set (y' := y) in H;
                            assert (~eq y' zero) by (subst y'; nonzero_tac)
                   end.
            rewrite ?ring_sub_definition, ?field_div_definition, <- ?mul_opp_l in f0.
            destruct prm.
            repeat first [ rewrite <- !mul_opp_l in f0
                         | rewrite !pull_inv_add in f0 by (intro; field_nonzero_mul_split; tauto)
                         | rewrite pull_inv_add_l in f0 by (intro; field_nonzero_mul_split; tauto)
                         | rewrite pull_inv_add_r in f0 by (intro; field_nonzero_mul_split; tauto) ].

            SearchAbout ring.
            2:intro; field_nonzero_mul_split; tauto. nsatz_contradict.
 2:clear f0; field_algebra.
            Focus 2.

            nsatz_contradict.
            Focus 2.
            { intro; repeat nsatz_nonzero_step.
            tauto.
2:clear f0.
2:intro.
Focus 2.
apply IntegralDomain.mul_nonzero_nonzero_cases in H1.
apply H.
2:nsatz_contradict.
2:simpl.
                         | rewrite pull_inv_add_l in f0
                         | rewrite pull_inv_add_r in f0pplyha  ].

            Lemma
            Print Ltac common_denominator_in.
            assert (H' : -
                    (((3 * xz) * (3 * xz^2 + a) / (2 * yx) -
                     (3 * xz) * (3 * xz^2 + a) / (2 * yx)) - yx) = - yx) .
            { rewrite <- f0; clear f0 H0 n.
              destruct prm.
              Print Ltac field_algebra.
              nsatz.
              field_algebra. }
            clear f0.
            rename H' into H''.
            assert (H' : -
                    (0 - yx) = - yx) .
            { rewrite <- H''; clear H'' H0 n.
              destruct prm.
              field_algebra. }
            clear H''.
            clear H0.
            apply n.
            nsatz.
            field_algebra.
            apply n.

            clear n H0 f0.

            field_algebra.
            clear f0.
              by
            field_simplify_eq_
            field_algebra.
            nsatz.
 by (clear f0 pfz pfx pfy; nsatz).
            apply n.
            { clear pfx.

replace a with (-(1+1+1)) in * by admit.
              replace d with (1+1+1) in * by admit.
              nsatz.
field_simplify_eq_all.

              repeat match goal with H : Feq _ _ |- _ => clear H end; bash.
              repeat match goal with H : Feq _ _ |- _ => clear H end; bash.
              repeat match goal with H : Feq _ _ |- _ => clear H end; bash.
              repeat match goal with H : Feq _ _ |- _ => clear H end; bash.
              repeat match goal with H : Feq _ _ |- _ => clear H end; bash.
              repeat match goal with H : Feq _ _ |- _ => clear H end; bash.
              repeat match goal with H : Feq _ _ |- _ => clear H end; bash.
bash.
              bash.
              bash.
            field_algebra.
          { repeat setoid_subst_rel Feq.
      {


      Focus 2.
      bash.
      apply @eq_dec.
     exact _.
      eapply @dec_and.
      1:bash.

      Focus 2.
      nsatz_contradict.
      Focus 4.
      { bash. }
        { cbv [sumwise fieldwise fieldwise' fst snd].
          setoid_subst_rel Feq.
          bash.
          field_algebra; try nsatz_contradict.
          field_algebra; try nsatz_contradict.
          bash.
          nsatz_contradict.
          exfalso; eauto using only_two_square_roots.
          neq_inv_to_neq Feq Fopp (eq_dec (eq := Feq)).
          lazymatch goal with
          | [ H : ~Feq ?x (Fopp ?y) |- _ ]
            => match goal with
               | [ H' : Feq x y |- _ ] => fail 1
               | [ H' : ~Feq x y |- _ ] => fail 1
               | _ => idtac
               end;
                 destruct (eq_dec x y)
          end.
          neq_inv_to_neq Feq Fopp eq_dec.
          repeat match goal with  H : ?R ?x ?x |- _ => let test := constr:(@Reflexive _ R) in clear H
          end.
          split.
          { match goal with
            |
field_algebra; [ | auto; nsatz_contradict.. ].


            3:auto.
            nsatz_contradict.
            field_algebra.

match goal with |- ?x = ?y => cut (x - y = 0) end.
            field_algebra.
            field_algebra.

            canonicalize_field_equalities.
intro; setoid_subst_rel Feq.
          Focus 2.
          field_algebra.
          field_algebra.
          nsatz_contradict.
          split.
          clear n0.
          clear n.
          clear pfy pfx.
          clear prm.
          clear d.
          generalize (2 * xx + xx); intro.
          generalize (3 * xx^2 + a); intro.
          generalize (2 * yx); intro.
          generalize (f0 * f1); intro.
          generalize (2 * yy); intro.
          generalize (f3 / f2); intro.
          generalize (f1^3 / f2^3); intro.
          generalize (f3 / f4); intro.
          generalize (f1^3/f4^3); intro.
          generalize (f5 - f6 - yx); intro.
          generalize (f7 - f8 - yy); intro.
          clear f0 f1 f2 f3 f4 f5 f6 f7 f8.
          revert dependent f9.
          revert dependent f10.
          revert dependent xx.

          try nsatz.

   try (solve [ neq01 | trivial | apply opp_nonzero_nonzero; trivial ]).
          Print Ltac field_algebra.
          split; field_algebra.
bash.
          nsatz_contradict.
          f

        2:bash.
      hnf.
      bash.
      field_algebra.
      destruct (eq_dec yy yx).
      { bash.
      rewrite <- pfx

      apply n.

      field_algebra.
      field_algebra.

      (* TODO: port denominator-nonzero proofs for associativity *)
      match goal with | |- _ <> 0 => admit end.
      match goal with | |- _ <> 0 => admit end.
      match goal with | |- _ <> 0 => admit end.
      match goal with | |- _ <> 0 => admit end.*)
    Admitted.
(*
    (* TODO: move to [Group] and [AbelianGroup] as appropriate *)
    Lemma mul_0_l : forall P, (0 * P = zero)%E.
    Proof. intros; reflexivity. Qed.
    Lemma mul_S_l : forall n P, (S n * P = P + n * P)%E.
    Proof. intros; reflexivity. Qed.
    Lemma mul_add_l : forall (n m:nat) (P:point), ((n + m)%nat * P = n * P + m * P)%E.
    Proof.
      induction n; intros;
        rewrite ?plus_Sn_m, ?plus_O_n, ?mul_S_l, ?left_identity, <-?associative, <-?IHn; reflexivity.
    Qed.
    Lemma mul_assoc : forall (n m : nat) P, (n * (m * P) = (n * m)%nat * P)%E.
    Proof.
      induction n; intros; [reflexivity|].
      rewrite ?mul_S_l, ?Mult.mult_succ_l, ?mul_add_l, ?IHn, commutative; reflexivity.
    Qed.
    Lemma mul_zero_r : forall m, (m * E.zero = E.zero)%E.
    Proof. induction m; rewrite ?mul_S_l, ?left_identity, ?IHm; try reflexivity. Qed.
    Lemma opp_mul : forall n P, (opp (n * P) = n * (opp P))%E.
    Admitted.

    Section PointCompression.
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
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv Fa Fd}
            {fieldF:@field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {Fprm:@twisted_weierstrass_params F Feq Fzero Fone Fadd Fmul Fa Fd}.
    Context {K Keq Kzero Kone Kopp Kadd Ksub Kmul Kinv Kdiv Ka Kd}
            {fieldK:@field K Keq Kzero Kone Kopp Kadd Ksub Kmul Kinv Kdiv}
            {Kprm:@twisted_weierstrass_params K Keq Kzero Kone Kadd Kmul Ka Kd}.
    Context {phi:F->K} {Hphi:@Ring.is_homomorphism F Feq Fone Fadd Fmul
                                                   K Keq Kone Kadd Kmul phi}.
    Context {Ha:Keq (phi Fa) Ka} {Hd:Keq (phi Fd) Kd}.
    Local Notation Fpoint := (@point F Feq Fone Fadd Fmul Fa Fd).
    Local Notation Kpoint := (@point K Keq Kone Kadd Kmul Ka Kd).

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
      let (x, y) := coordinates P in (phi x, phi y)) _.
    Next Obligation.
      destruct P as [[? ?] ?]; simpl.
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
             | [p: point |- _ ] => destruct p as [[??]?]
             | |- context[point_phi] => setoid_rewrite point_phi_correct
             | |- _ => progress cbv [fst snd coordinates proj1_sig eq fieldwise fieldwise' add zero opp ref_phi] in *
             | |- Keq ?x ?x => reflexivity
             | |- Keq ?x ?y => rewrite_strat bottomup hints field_homomorphism
             | [ H : Feq _ _ |- Keq (phi _) (phi _)] => solve [f_equiv; intuition]
             end.
      Qed.
  End Homomorphism.*)
End E.
