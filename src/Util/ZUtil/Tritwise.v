Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Bvector.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Stabilization.
Require Import Crypto.Util.ZUtil.Bitwise.
Require Import Crypto.Util.ZUtil.Testbit.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope bool_scope.
Local Open Scope Z_scope.

Create HintDb tritlist discriminated.

Module Import Tritlist.
  Local Set Primitive Projections.
  Local Notation trit := (option bool).
  Local Notation trit_repb v b := (match v with
                                   | Some b' => Bool.eqb b b'
                                   | None => true
                                   end).
  Local Notation trit_rep v b := (trit_repb v b = true).
  Record t := { internal_tritlist : list trit ; test_signtrit : trit }.
  Arguments option_map {_ _} & _ _.
  Definition signtrit (v : t) : option Z
    := option_map (fun b : bool => if b then -1 else 0) (test_signtrit v).
  (*Definition sgn (v : t) : Z
    := if test_signtrit v then -1 else if List.existsb (fun b => b) (tritlist v) then 1 else 0.*)
  Definition testtrit (v : t) (n : Z) : trit
    := if n <? 0
       then Some false
       else List.nth_default (test_signtrit v)
                             (internal_tritlist v)
                             (Z.to_nat n).
  Definition tritcount (v : t) : nat := List.length (internal_tritlist v).
  Hint Transparent tritcount : rewrite tritlist.
  Definition tritlist (v : t) (len : nat) : list trit
    := firstn len (internal_tritlist v) ++ repeat (test_signtrit v) (len - tritcount v).
  Notation tritlist_default v := (tritlist v (tritcount v)) (only parsing).
  Definition rep_t (v : t) (z : Bitlist.t) : Prop
    := (forall n, trit_rep (testtrit v n) (Bitlist.testbit z n))
       /\ trit_rep (test_signtrit v) (Bitlist.test_signbit z).
  Definition rep (v : t) (z : Z) : Prop
    := rep_t v (Bitlist.of_Z z).
  Definition trit_to_bit (val_if_none : bool) (v : trit) : bool
    := match v with
       | Some b => b
       | None => val_if_none
       end.
  Local Notation neg_sign_bit := true (only parsing).
  Local Notation pos_sign_bit := false (only parsing).
  Definition to_lower (v : t) : Bitlist.t
    := let sign_bit := trit_to_bit neg_sign_bit (test_signtrit v) in
       let default_bit := false (* having a 0 in any bit location moves a number more towards -∞ *) in
       Bitlist.Build_t
         (List.map (trit_to_bit default_bit) (tritlist_default v))
         sign_bit.
  Definition to_upper (v : t) : Bitlist.t
    := let sign_bit := trit_to_bit pos_sign_bit (test_signtrit v) in
       let default_bit := true (* having a 1 in any bit location moves a number more towards ∞ *) in
       Bitlist.Build_t
         (List.map (trit_to_bit default_bit) (tritlist_default v))
         sign_bit.
  Definition to_zrange (v : t) : zrange
    := {| lower := Bitlist.to_Z (to_lower v) ; upper := Bitlist.to_Z (to_upper v) |}.
  Definition range_bit_to_trit (l u : bool) : trit
    := if Bool.eqb l u then Some l else None.
  Fixpoint relax_tritlist (v : list trit) : list trit
    := match v with
       | nil => nil
       | v :: vs
         => (if existsb (fun o => match o with None => true | _ => false end) vs
             then None
             else v) :: relax_tritlist vs
       end.
  Definition relax (v : t) : t
    := Build_t match test_signtrit v with
               | Some _ => relax_tritlist (internal_tritlist v)
               | None => List.map (fun _ => None) (internal_tritlist v)
               end
               (test_signtrit v).
  Definition of_lower_upper (l u : Bitlist.t) : t
    := let len := Nat.max (Bitlist.bitcount l) (Bitlist.bitcount u) in
       relax
         (Build_t
            (List.map (fun '(lb, ub) => range_bit_to_trit lb ub)
                      (List.combine (Bitlist.bitlist l len) (Bitlist.bitlist u len)))
            (range_bit_to_trit (Bitlist.test_signbit l) (Bitlist.test_signbit u))).
  Definition of_zrange (v : zrange) : t
    := of_lower_upper (Bitlist.of_Z (lower v)) (Bitlist.of_Z (upper v)).

  Lemma length_relax_tritlist v : List.length (relax_tritlist v) = List.length v.
  Proof. induction v; cbn; lia. Qed.
  Hint Rewrite length_relax_tritlist : tritlist distr_length.

  Lemma tritcount_relax v : tritcount (relax v) = tritcount v.
  Proof.
    cbv [tritcount relax]; cbn [internal_tritlist]; break_innermost_match; now autorewrite with distr_length.
  Qed.
  Hint Rewrite tritcount_relax : tritlist.

  Lemma test_signtrit_relax v : test_signtrit (relax v) = test_signtrit v.
  Proof. reflexivity. Qed.
  Hint Rewrite test_signtrit_relax : tritlist.

  Lemma eq_internal_tritlist_default v : tritlist_default v = internal_tritlist v.
  Proof.
    cbv [tritcount tritlist].
    autorewrite with natsimplify; cbn [repeat].
    now rewrite firstn_all, List.app_nil_r by lia.
  Qed.

  Lemma testtrit_neg v n : n < 0 -> testtrit v n = Some false.
  Proof.
    cbv [testtrit]; break_innermost_match; Z.ltb_to_lt; try reflexivity; lia.
  Qed.

  Lemma enumerate_tritlist_default_eq v
    : enumerate (tritlist_default v) = List.combine (List.seq 0 (tritcount v)) (internal_tritlist v).
  Proof.
    rewrite eq_internal_tritlist_default.
    now cbv [enumerate tritcount]; autorewrite with distr_length.
  Qed.
  Hint Rewrite enumerate_tritlist_default_eq : tritlist.

  Lemma length_tritlist v len : length (tritlist v len) = len.
  Proof.
    cbv [tritlist tritcount]; autorewrite with distr_length.
    apply Nat.min_case_strong; try lia.
  Qed.
  Hint Rewrite length_tritlist : distr_length tritlist.

  Lemma nth_error_relax_tritlist n v
    : nth_error (relax_tritlist v) n
      = if existsb (fun o => match o with None => true | _ => false end) (skipn n v)
        then Some None
        else nth_error v n.
  Proof.
    revert n; induction v as [|v vs IH], n as [|n]; cbn; cbv [orb]; auto.
    now break_match.
  Qed.
  Hint Rewrite nth_error_relax_tritlist : tritlist.

  Lemma testtrit_relax v n
    : testtrit (relax v) n
      = if n <? 0
        then testtrit v n
        else if match test_signtrit v with None => true | _ => false end || (existsb (fun o => match o with None => true | _ => false end) (skipn (Z.to_nat n) (internal_tritlist v)))
             then None
             else testtrit v n.
  Proof.
    repeat first [ easy
                 | progress subst
                 | progress cbv [relax testtrit nth_default orb option_map] in *
                 | progress cbn [internal_tritlist test_signtrit] in *
                 | progress autorewrite with tritlist in *
                 | progress inversion_option
                 | rewrite !nth_error_map
                 | break_innermost_match_step
                 | break_innermost_match_hyps_step
                 | progress break_match ].
  Qed.
  Hint Rewrite testtrit_relax : tritlist.

  Lemma rep_impl_bounded_to_zrange v z
    : rep v z -> is_bounded_by_bool z (to_zrange v) = true.
  Proof.
    cbv [rep to_zrange].
    cbv [is_bounded_by_bool]; rewrite Bool.andb_true_iff, !Z.leb_le; cbn [lower upper].

    cbv [to_lower to_upper].
    Search Z.le Z.leb iff.
    cbv [rep_t].
    cbv [to_zrange].
  Admitted.

  Lemma rep_relax (v : t) (z : Z) : rep v z -> rep (relax v) z.
  Proof.
    intros [H1 H2]; split; [ clear H2; revert H1 | assumption ].
    autorewrite with tritlist bitlist.
    intros H n; specialize (H n); revert H.
    autorewrite with tritlist.
    now break_match.
  Qed.

  Lemma test_signtrit_of_lower_upper l u
    : test_signtrit (of_lower_upper l u)
      = if Bool.eqb (Bitlist.test_signbit l) (Bitlist.test_signbit u)
        then Some (Bitlist.test_signbit l)
        else None.
  Proof. reflexivity. Qed.
  Hint Rewrite test_signtrit_of_lower_upper : tritlist.

  Lemma test_signtrit_of_zrange v
    : test_signtrit (of_zrange v)
      = if Bool.eqb (lower v <? 0) (upper v <? 0)
        then Some (lower v <? 0)
        else None.
  Proof. now cbv [of_zrange]; autorewrite with tritlist bitlist. Qed.
  Hint Rewrite test_signtrit_of_zrange : tritlist.

  (*
  Lemma testtrit_of_zrange v n
    : testtrit (of_zrange v) n
      = if n <? 0
        then Some false
        else if existsb (fun o => match o with None => true | _ => false end) (skipn (Z.to_nat n) (internal_tritlist v))
             then None
             else testtrit v n.
*)
  Lemma rep_of_zrange (v : zrange) (z : Z)
    : is_bounded_by_bool z v = true -> rep (of_zrange v) z.
  Proof.
    pose proof (Z.stabilization_time_nonneg (lower v)).
    pose proof (Z.stabilization_time_nonneg (upper v)).
    cbv [is_bounded_by_bool]; intro; Bool.split_andb; Z.ltb_to_lt.
    cbv [rep rep_t]; split;
      [ | autorewrite with bitlist tritlist; cbv [Bool.eqb];
          break_innermost_match; Z.ltb_to_lt; try reflexivity; lia ].
    intro n.
    autorewrite with bitlist.
    (*
    cbv [of_zrange of_lower_upper].
    autorewrite with tritlist.
    cbv [testtrit]; cbn [internal_tritlist test_signtrit].
    Search testtrit.
    cbv [of_zrange].
    cbv [of_zrange of_lower_upper].
    intro H'; apply rep_relax; revert H'.
    autorewrite with bitlist; rewrite <- !Z2Nat.inj_max.
    cbv [rep rep_t]; cbn [test_signtrit].
    autorewrite with bitlist.
    split;
      [ | cbv [range_bit_to_trit Bool.eqb]; break_innermost_match; Z.ltb_to_lt; try reflexivity; lia ].
    rewrite Bool.andb_true_iff; intros [? ?
    cbv [rep].
    cbv [tritcount].
    cbn [test_signtrit tritlist].
    autorewrite with distr_length.
*)
    (*rewrite Nat.min_id, Z2Nat.id by (apply Z.max_case_strong; lia).*)
  Admitted.

  Definition values_of_trit (v : trit) : list bool
    := match v with
       | Some v => [v]
       | None => [true; false]
       end.

  Local Definition all_pairs {A B} (xs : list A) (ys : list B) : list (A * B)
    := List.flat_map (fun x => List.map (pair x) ys) xs.

  Definition lift_bitwise (f : bool -> bool -> bool) (x y : trit) : trit
    := let values := List.map (fun '(x, y) => f x y) (all_pairs (values_of_trit x) (values_of_trit y)) in
       if forallb (Bool.eqb true) values
       then Some true
       else if forallb (Bool.eqb false) values
            then Some false
            else None.

  Definition tritwise (f : bool -> bool -> bool) (v1 v2 : t) : t
    := let len := Nat.max (tritcount v1) (tritcount v2) in
       Build_t (List.map (fun '(a, b) => lift_bitwise f a b)
                         (List.combine (tritlist v1 len) (tritlist v2 len)))
               (lift_bitwise f (test_signtrit v1) (test_signtrit v2)).

  Lemma testtrit_tritwise f v1 v2 n : testtrit (tritwise f v1 v2) n = if n <? 0 then Some false else lift_bitwise f (testtrit v1 n) (testtrit v2 n).
  Proof.
    cbv [testtrit tritwise nth_default];
      cbn [internal_tritlist test_signtrit].
    rewrite nth_error_map, nth_error_combine.
    break_innermost_match_step; Z.ltb_to_lt; [ reflexivity | ].
    apply Nat.max_case_strong; intro.
    all: cbv [tritlist tritcount] in *;
      autorewrite with natsimplify;
      cbn [List.repeat]; rewrite List.app_nil_r, !firstn_all2, nth_error_app, nth_error_repeat_alt by lia.
    all: cbv [option_map].
    all: break_innermost_match.
    all: repeat first [ reflexivity
                      | progress inversion_option
                      | match goal with
                        | [ H : nth_error _ _ = None |- _ ] => apply nth_error_error_length in H; exfalso; lia
                        | [ H : context[nth_error _ _] |- _ ] => rewrite nth_error_length_error in H by lia
                        end ].
  Qed.
  Hint Rewrite testtrit_tritwise : tritlist.

  Lemma tritcount_tritwise f v1 v2
    : tritcount (tritwise f v1 v2) = Nat.max (tritcount v1) (tritcount v2).
  Proof. cbn; autorewrite with distr_length; lia. Qed.
  Hint Rewrite tritcount_tritwise : tritlist.

  Lemma lift_bitwise_rep f x y xb yb
    : trit_rep x xb -> trit_rep y yb -> trit_rep (lift_bitwise f x y) (f xb yb).
  Proof.
    repeat first [ progress destruct_head'_bool
                 | progress destruct_head' option
                 | progress cbv [lift_bitwise values_of_trit all_pairs andb] in *
                 | progress cbn [Bool.eqb List.map List.flat_map List.app List.forallb] in *
                 | progress intros
                 | congruence
                 | break_innermost_match_step ].
  Qed.

  Lemma tritwise_rep f x y xz yz
    : rep x xz -> rep y yz -> rep (tritwise f x y) (bitwise f xz yz).
  Proof.
    cbv [rep rep_t].
    intros [Hx Hx'] [Hy Hy']; split;
      [ revert Hx Hx' Hy Hy'; clear | revert Hx' Hy'; clear ];
      [ intros Hx Hx' Hy Hy' n; specialize (Hx n); specialize (Hy n);
        revert Hx Hy Hx' Hy'
      | cbv [bitwise tritwise lift_bitwise];
        cbn [test_signtrit] ];
      autorewrite with tritlist bitlist;
      [ destruct (n <? 0) eqn:?; [ reflexivity | Z.ltb_to_lt ]
      | destruct (xz <? 0), (yz <? 0), (test_signtrit x), (test_signtrit y);
        destruct_head'_bool; cbv;
        break_innermost_match; congruence ].
    (do 2 (break_innermost_match_step; rewrite ?Bool.eqb_true_iff, ?Bool.eqb_false_iff;
           intro; subst)).
    all: intros.
    all: match goal with
         | [ |- trit_rep (lift_bitwise ?f ?xv ?yv) (?f ?x ?y) ]
           => lazymatch xv with
              | None => destruct x
              | Some _ => idtac
              end;
                lazymatch yv with
                | None => destruct y
                | Some _ => idtac
                end
         end.
    all: cbv [lift_bitwise all_pairs values_of_trit List.forallb andb orb Bool.eqb List.flat_map List.map List.app];
      now break_innermost_match.
  Qed.
End Tritlist.
