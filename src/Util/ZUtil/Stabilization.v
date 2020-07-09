Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Hints.ZArith.
Require Import Crypto.Util.ZUtil.Tactics.ReplaceNegWithPos.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Testbit.
Require Import Crypto.Util.ZUtil.Shift.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SpecializeBy.

Local Open Scope Z_scope.

Notation stabilizes_after x l := (exists b, forall n, l < n -> Z.testbit x n = b).

Lemma stabilizes_after_Proper x
  : Proper (Z.le ==> Basics.impl) (fun l => stabilizes_after x l).
Proof.
  intros ?? H [b H']; exists b.
  intros n H''; apply (H' n); lia.
Qed.

Module Z.
  Notation stabilization_time x := (Z.max (Z.log2 (Z.pred (- x))) (Z.log2 x)).
  Notation stabilization_time_weaker x := (Z.log2_up (Z.abs x)).

  Lemma stabilization_time_nonneg x : 0 <= stabilization_time x.
  Proof. rewrite Z.max_le_iff; constructor; apply Z.log2_nonneg. Qed.
  Hint Resolve Z.stabilization_time_nonneg : zarith.

  Lemma stabilization_time_weaker_nonneg x : 0 <= stabilization_time_weaker x.
  Proof. apply Z.log2_up_nonneg. Qed.
  Hint Resolve Z.stabilization_time_weaker_nonneg : zarith.
End Z.
Hint Resolve Z.stabilization_time_nonneg Z.stabilization_time_weaker_nonneg : zarith.

Lemma stabilization_time (x:Z) : stabilizes_after x (Z.stabilization_time x).
Proof.
  destruct (Z_lt_le_dec x 0); eexists; intros;
    [ eapply Z.bits_above_log2_neg | eapply Z.bits_above_log2]; lia.
Qed.

Lemma stabilization_time_strict_alt (x:Z) : x <> 0 /\ x <> -1 -> Z.testbit x (Z.stabilization_time x) <> Z.testbit x (Z.succ (Z.stabilization_time x)).
Proof.
  intro.
  destruct (Z_dec' 0 x); destruct_head' sumbool; [ | | lia ];
    Z.replace_all_neg_with_pos;
    repeat first [ rewrite Z.bits_opp in * by lia
                 | rewrite Z.bits_above_log2 in * by lia
                 | rewrite Z.bit_log2 in * by lia
                 | progress cbn [negb] in *
                 | congruence
                 | match goal with
                   | [ |- context[Z.max ?x ?y] ]
                     => first [ rewrite (Z.max_l x y) by auto with zarith
                              | rewrite (Z.max_r x y) by auto with zarith ]
                   | [ |- context[Z.log2 ?x] ]
                     => rewrite (Z.log2_nonpos x) by lia
                   end ].
Qed.

Lemma stabilization_time_strict (x:Z) : x <> 0 /\ x <> -1 -> forall t, t < Z.stabilization_time x -> ~stabilizes_after x t.
Proof.
  intros Hx t Ht [b Hs].
  pose proof (Hs (Z.stabilization_time x) ltac:(lia)) as Hs1.
  pose proof (Hs (Z.succ (Z.stabilization_time x)) ltac:(lia)) as Hs2.
  pose proof (stabilization_time_strict_alt x Hx).
  congruence.
Qed.

Lemma stabilization_time_weaker (x:Z) : stabilizes_after x (Z.stabilization_time_weaker x).
Proof.
  eapply stabilizes_after_Proper; try apply stabilization_time.
  repeat match goal with
         | [ |- context[Z.abs _ ] ] => apply Zabs_ind; intro
         | [ |- context[Z.log2 ?x] ]
           => rewrite (Z.log2_nonpos x) by lia
         | [ |- context[Z.log2_up ?x] ]
           => rewrite (Z.log2_up_nonpos x) by lia
         | _ => rewrite Z.max_r by auto with zarith
         | _ => rewrite Z.max_l by auto with zarith
         | _ => etransitivity; [ apply Z.le_log2_log2_up | lia ]
         | _ => progress Z.replace_all_neg_with_pos
         | [ H : 0 <= ?x |- _ ]
           => assert (x = 0 \/ x = 1 \/ 1 < x) by lia; clear H; destruct_head' or; subst
         | _ => lia
         | _ => simpl; lia
         | _ => rewrite Z.log2_up_eqn by assumption
         | _ => progress change (Z.log2_up 1) with 0
         end.
Qed.

Lemma land_stabilizes (a b la lb:Z) (Ha:stabilizes_after a la) (Hb:stabilizes_after b lb) : stabilizes_after (Z.land a b) (Z.max la lb).
Proof.
  destruct Ha as [ba Hba]. destruct Hb as [bb Hbb].
  exists (andb ba bb); intros n Hn.
  rewrite Z.land_spec, Hba, Hbb; trivial; lia.
Qed.

Lemma lor_stabilizes (a b la lb:Z) (Ha:stabilizes_after a la) (Hb:stabilizes_after b lb) : stabilizes_after (Z.lor a b) (Z.max la lb).
Proof.
  destruct Ha as [ba Hba]. destruct Hb as [bb Hbb].
  exists (orb ba bb); intros n Hn.
  rewrite Z.lor_spec, Hba, Hbb; trivial; lia.
Qed.

Local Arguments Z.pow !_ !_.
Local Arguments Z.log2_up !_.
Local Arguments Z.add !_ !_.
Lemma testbit_nonneg_iff x
  : (exists l, 0 <= l /\ forall n : Z, l < n -> Z.testbit x n = false) <-> 0 <= x.
Proof.
  split; intro H.
  { destruct H as [l [Hl H]].
    edestruct Z_lt_le_dec; [ | eassumption ].
    pose proof (fun pf n => Z.bits_above_log2_neg x n pf) as H'.
    specialize_by (lia || assumption).
    specialize (H (1 + Z.max l (Z.log2 (Z.pred (- x))))).
    specialize (H' (1 + Z.max l (Z.log2 (Z.pred (- x))))).
    specialize_by (apply Z.max_case_strong; lia).
    congruence. }
  { pose proof (fun n => Z.bits_above_log2 x n H) as Hf.
    eexists; split; [ | eapply Hf ]; auto with zarith. }
Qed.

Lemma stabilizes_bounded_pos (x l:Z) (H:stabilizes_after x l) (Hl : 0 <= l) (Hx : 0 < x)
  : x <= 2^(l + 1) - 1.
Proof.
  assert (Hlt : forall l n, l < n <-> l + 1 <= n) by (intros; lia).
  destruct H as [b H].
  destruct (proj2 (testbit_nonneg_iff x)) as [l' [H0' H1']]; [ lia | ].
  pose proof (Z.testbit_false_bound x (l' + 1)) as Hf.
  pose proof (Z.testbit_false_bound x (l + 1)) as Hf'.
  pose proof (fun pf n => Z.bits_above_log2 x n pf) as Hf''.
  pose proof (fun pf n => Z.log2_lt_pow2 x n pf) as Hlg.
  specialize_by lia.
  setoid_rewrite <- Z.le_ngt in Hf.
  setoid_rewrite <- Z.le_ngt in Hf'.
  setoid_rewrite <- Hlt in Hf; setoid_rewrite <- Hlt in Hf'; clear Hlt.
  setoid_rewrite <- Hlg in Hf''; clear Hlg.
  destruct b; specialize_by (lia || assumption); [ | lia ].
  specialize (H (1 + Z.max l l')).
  specialize (H1' (1 + Z.max l l')).
  specialize_by (apply Z.max_case_strong; lia).
  congruence.
Qed.

Lemma stabilizes_bounded (x l:Z) (H:stabilizes_after x l) (Hl : 0 <= l) : Z.abs x <= 2^(1 + l).
Proof.
  assert (Hlt : forall l n, l < n <-> l + 1 <= n) by (intros; lia).
  rewrite Z.add_comm.
  destruct (Z_zerop x); subst; simpl.
  { cut (0 < 2^(l + 1)); auto with zarith. }
  apply Zabs_ind; intro.
  { etransitivity; [ apply stabilizes_bounded_pos; eauto | ]; lia. }
  { Z.replace_all_neg_with_pos.
    destruct (Z.eq_dec x 1); subst.
    { assert (1 < 2^(l+1)) by auto with zarith.
      lia. }
    { assert (H' : stabilizes_after (Z.pred x) l).
      { destruct H as [b H]; exists (negb b).
        do 2 let x := fresh in intro x; specialize (H x).
        rewrite Z.bits_opp in H by lia.
        destruct b; rewrite ?Bool.negb_true_iff, ?Bool.negb_false_iff in H; assumption. }
      clear H.
      apply stabilizes_bounded_pos in H'; auto; lia. } }
Qed.

Lemma compare_by_bits z1 z2 c
      (d := Z.lxor z1 z2)
      (l := if ((d =? 0) || (d =? -1))%Z%bool then 0 else Z.stabilization_time d)
  : Z.compare z1 z2 = c
    <-> ((forall n, 0 <= n -> Z.bit_compare (Z.testbit z1 n) (Z.testbit z2 n) = c)
         \/ (c <> Eq
             /\ (forall n, l < n -> Z.bit_compare (Z.testbit z1 n) (Z.testbit z2 n) = Eq)
             /\ Z.bit_compare (Z.testbit z1 l) (Z.testbit z2 l) = c)).
Proof.
  pose proof (Z.stabilization_time_nonneg d) as Hs.
  pose proof (stabilization_time d) as Hs'.
  pose proof (stabilization_time_strict_alt d) as Hs''.
  pose proof (Z.lxor_eq z1 z2) as Hlxor.
  subst l d.
  generalize dependent (Z.stabilization_time (Z.lxor z1 z2)); intro l; intros.
  cbv beta zeta.
  split; [ | intros [H|H]; [ now apply Z.compare_by_bits_impl | ] ];
    destruct (Z.compare_spec z1 z2);
    repeat first [ progress intros
                 | progress subst
                 | rewrite Z.bit_compare_refl in *
                 | reflexivity
                 | congruence
                 | lia
                 | progress destruct_head'_and
                 | progress destruct_head'_or
                 | progress destruct_head'_ex
                 | progress autorewrite with Ztestbit in *
                 | progress Z.ltb_to_lt
                 | progress rewrite ?Bool.andb_false_r, ?Bool.orb_false_r, ?Bool.orb_true_iff in *
                 | match goal with
                   | [ |- _ \/ ((?x <> ?x) /\ _) ] => left
                   | [ H : ?x + ?y < ?x + ?z |- _ ] => assert (y < z) by (clear -H; lia); clear H
                   | [ H : forall n, Z.bit_compare (Z.testbit ?x n) (Z.testbit ?x n) = _ |- _ ]
                     => specialize (H 0)
                   | [ |- ?A \/ ((_ <> _) /\ ?B) ]
                     => cut (A \/ B); [ intros [?|?]; [ left | right; split ]; auto; congruence | ]
                   | [ |- context[Z.bit_compare ?x ?y] ] => destruct (bit_compare x y) eqn:?
                   | [ H : context[Z.bit_compare _ _ = ?c] |- _ ]
                     => lazymatch c with
                        | Eq => setoid_rewrite Z.bit_compare_eq_iff in H
                        | Gt => setoid_rewrite Z.bit_compare_gt_iff in H
                        | Lt => setoid_rewrite Z.bit_compare_lt_iff in H
                        end
                   | [ |- context[Z.bit_compare _ _ = ?c] ]
                     => lazymatch c with
                        | Eq => setoid_rewrite Z.bit_compare_eq_iff
                        | Gt => setoid_rewrite Z.bit_compare_gt_iff
                        | Lt => setoid_rewrite Z.bit_compare_lt_iff
                        end
                   | [ H : context[if ?x then _ else _] |- _ ]
                     => destruct x eqn:?; rewrite ?Bool.orb_false_iff, ?Z.eqb_eq_iff in *; specialize_by_assumption; subst; try congruence
                   | [ |- context[if ?x then _ else _] ]
                     => destruct x eqn:?; rewrite ?Bool.orb_false_iff, ?Z.eqb_eq_iff in *; specialize_by_assumption; subst; try congruence
                   | [ H : ?x < ?y |- _ ]
                     => is_var x; is_var y; rewrite (Z.add_shift_land_ones x (l + 1)), (Z.add_shift_land_ones y (l + 1)) in H by lia
                   | [ H0 : forall n, ?l < n -> Z.testbit ?z1 n = Z.testbit ?z2 n,
                         H1 : forall m, ?l < m -> Z.testbit (Z.lxor ?z1 ?z2) _ = _ |- _ ]
                     => is_var z1; is_var z2;
                        rewrite (Z.lor_shift_land_ones z1 (l + 1)), (Z.lor_shift_land_ones z2 (l + 1)) in H0, H1 by lia;
                        specialize (fun n (pf : 0 <= n) => H0 (n + (l + 1)) ltac:(lia));
                        specialize (fun n (pf : 0 <= n) => H1 (n + (l + 1)) ltac:(lia));
                        assert ((z1 >> (l+1)) = (z2 >> (l+1)));
                        generalize dependent (z1 >> (l+1)); generalize dependent (z2 >> (l+1)); intros;
                        [ apply Z.bits_inj';
                          let n := fresh "n" in
                          let pf := fresh in
                          intros n pf; specialize (H0 n pf);
                          progress autorewrite with Ztestbit Ztestbit_full zsimplify_fast in H0, H1;
                          break_innermost_match_hyps
                        | subst; clear H ]
                   | [ H : Z.lxor _ _ = -1 |- _ \/ _ ] => left
                   | [ H : Z.lxor ?x ?y = -1, H' : forall n, ?v < n -> Z.testbit ?x n = Z.testbit ?y n |- _ ]
                     => exfalso;
                        clear -H H';
                        let n := constr:(Z.succ v) in
                        specialize (H' n ltac:(lia));
                        let H'' := fresh in
                        pose proof (f_equal (fun v' => Z.testbit v' n) H) as H'';
                        cbv beta in H'';
                        change (-1) with (-(1)) in H'';
                        autorewrite with Ztestbit in H'';
                        (destruct (Z.testbit x n) eqn:?, (Z.testbit y n) eqn:?);
                        cbn [xorb] in H''; congruence
                   end ].
  5: {
    lazymatch goal with
    end.


    lazymatch goal with
                   | [ H : Z.lxor ?x ?y = -1 |- context[Z.testbit ?x ?n] ]
                     => let H' := fresh in
                        pose proof (f_equal (fun v => Z.testbit v n) H) as H';
                          cbv beta in H';
                        change (-1) with (-(1)) in H';
                        autorewrite with Ztestbit in H';
                        (destruct (Z.testbit x n) eqn:?, (Z.testbit y n) eqn:?);
                        cbn [xorb] in H'; try congruence
    end.
    reflexivity.

    reflexivity.
    cbn.
    Search (Z.testbit (-(1))).
  match goal with
  end.
  Search Z.lxor Z.testbit.
  Search (Z.lxor _ _ = -1).
  rewrite Bool.orb_true_iff in *.
  6: {
  4: { match goal with
       end.
    match goal with
       | [ H : ?x &' Z.ones ?n < ?y &' Z.ones ?n |- _ ]
         => let x' := constr:(x &' Z.ones n) in
            let y' := constr:(y &' Z.ones n) in
            pose proof (Z.testbit_spec x' (l+1))
       end.
                   | [ H : forall n, 0 <= n -> Z.testbit ?v _ = _ |- _ ]
                     => (tryif is_var v
                          then fail
                          else (let H' := fresh in
                                eassert (forall n, 0 <= n -> _);
                                [ let n := fresh in
                                  let pf := fresh in
                                  intros n pf; specialize (H n pf);
                                  progress autorewrite with Ztestbit Ztestbit_full zsimplify_fast in H;
                                  break_innermost_match_hyps; try solve [ exfalso; lia ]; [];
                                  rewrite ?Bool.andb_false_r, ?Bool.orb_false_r, ?Bool.xorb_nilpotent in H;
                                  refine H
                                | clear H ]))
                   end ].
  3: {
    lazymatch goal with

       end.
       Search (xorb ?x ?x).
    lazymatch goal with
    | [ H0 : forall n, ?l < n -> Z.testbit ?z1 n = Z.testbit ?z2 n,
          H1 : forall m, ?l < m -> Z.testbit (Z.lxor ?z1 ?z2) _ = _ |- _ ]
      => is_var z1; is_var z2;
         rewrite (Z.lor_shift_land_ones z1 (l + 1)), (Z.lor_shift_land_ones z2 (l + 1)) in H0, H1 by lia;
         specialize (fun n (pf : 0 <= n) => H0 (n + (l + 1)) ltac:(lia));
         specialize (fun n (pf : 0 <= n) => H1 (n + (l + 1)) ltac:(lia));
         assert ((z1 >> (l+1)) = (z2 >> (l+1)));
         generalize dependent (z1 >> (l+1)); generalize dependent (z2 >> (l+1)); intros;
         [ apply Z.bits_inj';
           let n := fresh "n" in
           let pf := fresh in
           intros n pf; specialize (H0 n pf);
           s autorewrite with Ztestbit Ztestbit_full zsimplify_fast in H;
                          break_innermost_match_hyps
                        | subst; clear H ]
                   end.
    end.
    2: {

      break_innermost_match_hyps; try solve [ exfalso; lia ]; [];
       H;
    Search Z.testbit (@eq Z).
         let H' := fresh in
         eassert (H' : forall n, 0 <= n -> _);
           [ let n := fresh "n" in
           let pf := fresh in
           intros n pf; specialize (H n pf);

           refine H
         | ]
    end.

    edestruct Z_lt_dec.

    eassert _.
    Search (?x = _ + (Z.land ?x _))%Z.
    lazymatch goal with
    end.
      assert (H' : forall n,
                    l < n
                    -> Z.testbit (Z.lor (z1 >> x) << x + (z1 &' Z.ones x)) n
                       = Z.testbit ((z2 >> x) << x + (z2 &' Z.ones x)) n)
           by (intros; rewrite <- !Z.add_shift_land_ones by lia; auto);
           assert (forall n, 0 <= n -> Z.testbit (z1 >> offset) n = Z.testbit (z2 >> offset) n);
           [ let n := fresh "n" in
             let pf := fresh in
             intros n pf; specialize (H' (n + offset) ltac:(lia))
           | ]
    end.
    autorewrite with Ztestbit Ztestbit_full in H2.
         assert (forall n, 0 <= n -> Z.testbit (z1 >> offset) n = Z.testbit (z2 >> offset) n);
           [ let n := fresh "n" in
             let pf := fresh in
             intros n pf; specialize (H (n + offset) ltac:(lia));
             rewrite (Z.add_shift_land_ones z1 x), (Z.add_shift_land_ones z2 x) in H
           | ]
    end.
      rewrite (lor_shift_land_ones z1 x), (lor_shift_land_ones z2 x) in * by lia
    end.
    assert (forall n, 0 <= n -> Z.testbit (z1 >> x) n = Z.testbit (z2 >> x)
      autorewrite with Ztestbit_full in H2.
             let H1 := fresh in
             let H2 := fresh in
             pose proof (Z.div_mod z1 (2^x) ltac:(lia)) as H1;
               pose proof (Z.div_mod z2 (2^x) ltac:(lia)) as H2;
               rewrite Z.mul_comm in H1, H2;
               rewrite <- !Z.shiftl_mul_pow2, <- !Z.shiftr_div_pow2, <- !Z.land_ones in H1, H2 by lia;
               rewrite H1, H2 in H
      end.
      Search Z.add Z.lor.
      Search (?z = Z.lor _ _).
      Search Z.add Z.lor.
      Search Z.testbit Z.lor.
      Search (Z.testbit (_ + _)).
      Search (_ mod 2^_) Z.land.
      Search (0 < _^_).
    4: {
    3: { match goal with

         end.
    2: {

    {
      2: {
    pose proof
    Search Z.compare.
           \/ ((forall n, l <= n -> bit_compare (Z.testbit z1 n) (Z.testbit z2 n) = Eq)
               /\
           \/ ((exists l, forall n, l <= n -> bit_compare (Z.testbit z1 n) (Z.testbit z2 n) = Eq)
               /\
