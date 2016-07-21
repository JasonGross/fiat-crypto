(*** Barrett Reduction *)
(** This file implements Barrett Reduction on [Z].  We follow Wikipedia. *)
Require Import Coq.ZArith.ZArith Coq.micromega.Psatz.
Require Import Crypto.Util.ZUtil Crypto.Util.Tactics Crypto.Algebra.

Local Open Scope Z_scope.

Section barrett.
  Context (n a : Z)
          (n_reasonable : n <> 0).
  (** Quoting Wikipedia <https://en.wikipedia.org/wiki/Barrett_reduction>: *)
  (** In modular arithmetic, Barrett reduction is a reduction
      algorithm introduced in 1986 by P.D. Barrett. A naive way of
      computing *)
  (** [c = a mod n] *)
  (** would be to use a fast division algorithm. Barrett reduction is
      an algorithm designed to optimize this operation assuming [n] is
      constant, and [a < n²], replacing divisions by
      multiplications. *)

  (** * General idea *)
  Section general_idea.
    (** Let [m = 1 / n] be the inverse of [n] as a floating point
        number. Then *)
    (** [a mod n = a - ⌊a m⌋ n] *)
    (** where [⌊ x ⌋] denotes the floor function. The result is exact,
        as long as [m] is computed with sufficient accuracy. *)

    (* [/] is [Z.div], which means truncated division *)
    Local Notation "⌊am⌋" := (a / n) (only parsing).

    Theorem naive_barrett_reduction_correct
      : a mod n = a - ⌊am⌋ * n.
    Proof.
      apply Zmod_eq_full; assumption.
    Qed.
  End general_idea.

  (** * Barrett algorithm *)
  Section barrett_algorithm.
    (** Barrett algorithm is a fixed-point analog which expresses
        everything in terms of integers. Let [k] be the smallest
        integer such that [2ᵏ > n]. Think of [n] as representing the
        fixed-point number [n 2⁻ᵏ]. We precompute [m] such that [m =
        ⌊4ᵏ / n⌋]. Then [m] represents the fixed-point number
        [m 2⁻ᵏ ≈ (n 2⁻ᵏ)⁻¹]. *)
    (** N.B. We don't need [k] to be the smallest such integer. *)
    Context (k : Z)
            (k_good : n < 2 ^ k)
            (m : Z)
            (m_good : m = 4^(k-1) / n). (* [/] is [Z.div], which is truncated *)
    (** Wikipedia neglects to mention non-negativity, but we need it.
        It might be possible to do with a relaxed assumption, such as
        the sign of [a] and the sign of [n] being the same; but I
        figured it wasn't worth it. *)
    Context (n_pos : 0 < n) (* or just [0 <= n], since we have [n <> 0] above *)
            (a_nonneg : 0 <= a).

    Lemma k_nonnegative : 0 <= k.
    Proof.
      destruct (Z_lt_le_dec k 0); try assumption.
      rewrite !Z.pow_neg_r in * by lia; lia.
    Qed.

    (** Now *)
    (*Goal a < 2^(2 * k - 2) -> m < 2^(k-1) -> (m * a) / 4^k = (m * (a / 2^(k-2))) / 2^k.
    Proof.
      intros.*)

    Context (a_really_small : a < 2^(2 * k - 2))
            (m_really_small : m < 2^k)
            (n_really_small : n < 2^(k-1))
            (k_big_enough : 2 <= k).
    Let q := (m * (a / 2^(k-2))) / 2^k.
    Let r := a - q * n.
    (** Because of the floor function (in Coq, because [/] means
        truncated division), [q] is an integer and [r ≡ a mod n]. *)
    Theorem barrett_reduction_equivalent
      : r mod n = a mod n.
    Proof.
      subst r q m.
      rewrite <- !Z.add_opp_r, !Zopp_mult_distr_l, !Z_mod_plus_full by assumption.
      reflexivity.
    Qed.

    Lemma qn_small
      : q * n <= a.
    Proof.
      (*pose proof k_nonnegative; subst q r m.
      assert (0 <= 2^(k-1)) by zero_bounds.
      Z.simplify_fractions_le.
    Qed.*)
      Admitted.

    (** Also, if [a < n²] then [r < 2n]. *)
    (** N.B. It turns out that it is sufficient to assume [a < 4ᵏ]. *)
    Context (a_small : a < 4^k).
    Lemma q_nice : { b : bool | q = a / n + if b then -1 else 0 }.
    Proof.
      Notation "x 'ᵏ'" := (x ^ k) (format "x 'ᵏ'", at level 10).
      Notation "x 'ᵏ' '⁻' '¹'" := (x ^ (k-1)) (format "x 'ᵏ' '⁻' '¹'", at level 10).
      Notation "x 'ᵏ' '⁻' '²'" := (x ^ (k-2)) (format "x 'ᵏ' '⁻' '²'", at level 10).
      Notation "x '²ᵏ' '⁻' '²'" := (x ^ (2 * k-2)) (format "x '²ᵏ' '⁻' '²'", at level 10).
      Require Import Utf8.
      Infix "≤" := Z.le.
      assert (0 <= (4 ^ k * a / n) mod 4 ^ k < 4 ^ k) by auto with zarith lia.
      assert (0 <= a * (4 ^ k mod n) / n < 4 ^ k) by (auto with zero_bounds zarith lia).
      assert (0 <= a / 2 ^ (k - 2)) by zero_bounds.
      assert (0 < 2^(k-2)) by auto with zarith lia.
      assert (a / 2^(k-2) <= 2^(2*k - 2) / 2^(k-2)) by auto with zarith lia.
      assert (a / 2 ^ (k - 2) <= 2^k) by (autorewrite with pull_Zpow zsimplify in *; assumption).
      subst q r m.
      assert (2^(k-2) < n < 2^(k-1)).
      { assert (2^(k-2) <= n < 2^(k-1)).
        { split; try lia.
          move m_really_small at bottom.
          destruct (Z_lt_le_dec n (2^(k-2))) as [H'|H']; [ | assumption ].
          pose proof (fun H0 H1 => @Zdiv_le_compat_l (4^(k-1)) _ _ H0 (conj H1 H')) as H''.
          specialize_by ltac:(auto with zarith lia).
          contradict H''.
          change 4 with (2^2) at 1.
          rewrite <- Z.pow_mul_r by lia.
          autorewrite with pull_Zpow.
          ring_simplify_subterms.
          lia. }
        assert (n <> 2^(k-2)).
        { intro; subst.
          revert m_really_small.
          change 4 with (2^2).
          rewrite <- Z.pow_mul_r by lia.
          autorewrite with pull_Zpow.
          ring_simplify_subterms.
          lia. }
        lia. }
      rewrite (Z.div_mul_diff_exact''' (4^(k-1)) n (a/2^(k-2))) by auto with lia zero_bounds.
      rewrite (Z_div_mod_eq (4^(k-1) * _ / n) (2^k)) by lia.
      autorewrite with push_Zmul push_Zopp zsimplify zstrip_div.
      set (v := 4^(k-1)) at 1.
      replace v with (2^k*2^(k-2)) by (change 4 with (2^2) in v; subst v; rewrite <- Z.pow_mul_r by lia; autorewrite with pull_Zpow; ring_simplify_subterms; reflexivity); clear v.
      rewrite <- !Z.mul_assoc.
      autorewrite with push_Zmul push_Zopp zsimplify zstrip_div.
      change 4 with (2^2) in *.
      ring_simplify_subterms.
      rewrite (Z.mul_comm (a/2^(k-2))).

      rewrite Z.div_sub_small; [ | split; auto with zero_bounds zarith lia.. ].
      rewrite Z.mul_div_eq by lia.
      rewrite <- Z.pow_mul_r in * by lia.
      replace (2^(2*(k-1))) with (2^k * 2^(k-2)) in m_really_small by admit.
      assert (2^(k-2) <= n) by admit.
      assert (0 <= a mod 2^(k-2) < 2^(k-2)) by auto with zarith.
      assert (a mod 2^(k-2) < n) by lia.
      replace (2^(2*(k-1))) with (2^k * 2^(k-2)) by (autorewrite with pull_Zpow; auto with zarith lia).



      rewrite <- !Z.mul_assoc.
      rewrite Z.mul_div_eq by lia.
      autorewrite with pull_Zpow.
      ring_simplify (k + (k - 2)).
      rewrite (Z.mul_comm (a / _) (_ mod _)).
      Notation "x 'ᵏ'" := (x ^ k) (format "x 'ᵏ'", at level 10).
      Notation "x 'ᵏ' '⁻' '²'" := (x ^ (k-2)) (format "x 'ᵏ' '⁻' '²'", at level 10).
      Notation "x '²ᵏ' '⁻' '²'" := (x ^ (2 * k-2)) (format "x '²ᵏ' '⁻' '²'", at level 10).
      ring_simplify_subterms.

      Print Rewrite HintDb pull_Zpow.
      SearchAbout (_^_ * _^_).

      SearchAbout ((_^_)^_).
      autorewrite with zsimplify.
      simpl.
      unfold Z.pow_pos.
      unfold Pos.iter.
      simpl.

      SearchAbout (_ -
      autorewrite with zsimplify.
      move m_really_small at bottom.
      rewrite <- Z.pow_mul_r in * by lia.
      SearchAbout (_/_ <= _).
      autorewrite with _Zpow in *.
      SearchAbout (?x * (?y / ?x)).
      autorewrite with push_Zmul push_Zopp zsimplify zstrip_div.
            repeat match goal with
             | [ |- context[?x] ]
               => let x' := fresh in
                  evar (x' : Z);
                    replace x with x' by (progress ring_simplify; subst x'; reflexivity);
                    subst x'
             end.


      Focus 2.
      SearchAbout (?x * ?y / ?z) (?y < ?z).
      zero_bounds.
      F

      autorewrite with push_Zmul push_Zopp zsimplify zstrip_div.
      rewrite Z.div_div by lia.
      rewrite <- (Z.mul_comm n).
      rewrite <- Z.div_div by lia.
      rewrite Z.mul_div_eq by lia.

      autorewrite with push_Zmul push_Zopp zsimplify zstrip_div.
      replace (2 ^ 2 * (2 ^ k * (a / n))) with (2 ^ k * (2 ^ 2 * (a / n))) by lia.
      rewrite <- !Z.add_opp_r.
      rewrite <- !Z.add_assoc.
      autorewrite with push_Zmul push_Zopp zsimplify zstrip_div.
      eexists.
      ring_simplify.
      repeat match goal with
             | [ |- context[?x] ]
               => let x' := fresh in
                  evar (x' : Z);
                    replace x with x' by (progress ring_simplify; subst x'; reflexivity);
                    subst x'
             end.
      replace k with 8 in * by admit.
      replace n with (2^7+1) in * by admit.
      replace a with (2^12) in * by admit.
      compute in * |- .

      compute in * |- .
      clear n_reasonable.

      repeat match goal with
             | [ |- context[?x] ]
               => let x' := fresh in
                  evar (x' : Z);
                    replace x with x' by (progress ring_simplify; subst x'; reflexivity);
                    subst x'
             end.
      simpl Z.mul.
      simpl Z.div.
      simpl Z.opp.
      simpl Z.div.
      ring_simplify.
      etransitivity; [ simpl; reflexivity | ].
      change (5/3) with 1.
      set (v := -2048/256 + 8).
      simpl in v.
      subst v.
      change (6/3) with 2.
      simpl Z.div.

      simpl Z..
      ring_simplify.
        match goal with
        eexists; ring_simplify.
      evar (x : Z).

      Fail match goal with
      | [ |- context[?x] ]
        => let x' := fresh in
           evar (x' : Z);
             idtac x; replace x with x' by (subst x'; progress ring_simplify; reflexivity);
             subst x'
      end.
                                   r

      SearchAbout (?x * (_ / ?x)).
      pose (fun x => Z.div_mod_eq (x / n) (2^(k-2))).
      rewrite (Z_div_mod_eq (_ / n) (2^(k-2))) at 1 by lia.
      autorewrite with push_Zmul push_Zopp zsimplify zstrip_div.
      SearchAbout

      2:lia.
      2:lia.

      2:lia.
      2:lia.
      2:lia.
      autorewrite with push_Zmul push_Zopp zsimplify zstrip_div.
      repeat match goal with
             | [ |- context[?x / (?y ^ ?z) * ?y ^ ?w] ]
               => replace (x / (y^z) * y^w) with (if z <=? w then (x - x mod y^z) * y^(w-z) else (x - x mod y^z) / y^(z-w)) by admit
             | [ |- context[2 * ?x - ?x] ]
               => replace (2 * x - x) with x by lia
             | [ |- context[2 * ?x - (?x - ?y)] ]
               => replace (2 * x - (x - y)) with (x + y) by lia
             | [ |- context[?x - 2 <=? 2 * ?x] ]
               => replace (x - 2 <=? 2 * x) with true by admit
             end.
      eexists; reflexivity.
    Qed.

    Lemma r_small : r < 2 * n.
    Proof.
      Hint Rewrite (Z.mul_div_eq' a n) using lia : zstrip_div.
      assert (a mod n < n) by auto with zarith lia.
      subst r; rewrite (proj2_sig q_nice); generalize (proj1_sig q_nice); intro; subst q m.
      autorewrite with push_Zmul zsimplify zstrip_div.
      break_match; auto with lia.
    Qed.



    Lemma r_small : r < 2 * n.
    Proof.
      (** TODO: move me *)
      Hint Resolve Z.pow_nonzero Z.mul_pos_pos : zarith.
      Hint Rewrite (Z.div_small a (4^k)) (Z.mod_small a (4^k)) using lia : zsimplify.
      Hint Rewrite (Z.mul_div_eq' a n) using lia : zstrip_div.
      cut (r + 1 <= 2 * n); [ lia | ].
      pose proof k_nonnegative; subst r q m.
      assert (0 <= 2^(k-1)) by zero_bounds.
      assert (0 <= a / 2^(k-2)) by zero_bounds.
      assert (4^k <> 0) by auto with zarith lia.
      assert (0 <= k-2) by lia.
      assert (2^(k-2) <> 0) by auto with zarith lia.
      assert (2^k <> 0) by auto with zarith lia.
      assert (a mod n < n) by auto with zarith lia.
      assert (0 < 2^k*2^k) by auto with zarith lia.
      pose proof (Z.mod_pos_bound (a * 4^k / n) (4^k)).
      transitivity (a - ((a / 2^(k-2)) * 4 ^ k / n - (a / 2^(k-2))) / 2 ^ k * n + 1).
      { rewrite <- (Z.mul_comm (a / _));  eauto 6 with zarith lia. }
      replace (4^k) with (2^(2 * k)) by admit.
      repeat match goal with
             | [ |- context[?x / (?y ^ ?z) * ?y ^ ?w] ]
               => replace (x / (y^z) * y^w) with (if z <=? w then (x - x mod y^z) * y^(w-z) else (x - x mod y^z) / y^(z-w)) by admit
             | [ |- context[2 * ?x - ?x] ]
               => replace (2 * x - x) with x by lia
             | [ |- context[2 * ?x - (?x - ?y)] ]
               => replace (2 * x - (x - y)) with (x + y) by lia
             | [ |- context[?x - 2 <=? 2 * ?x] ]
               => replace (x - 2 <=? 2 * x) with true by admit
             end.
      unfold "<=?".

      SearchAbout (
      repeat match goal with
             | [ |- context[?x / ?y] ]
               => let x_over_y := fresh x in
                  set (x_over_y := x / y);
                    rewrite (@Z.div_mod x y) by lia;
                    change (x/y) with x_over_y
             end.

             replace x with (y +

      rewrite Z.mul_div_eq by lia.

      rewrite (Z_div_mod_eq (_ * 4^k / n) (4^k)) by lia.
      replace (2^k) with (2^(k-2)*2^2) by (rewrite <- Z.pow_add_r by lia; apply f_equal2; lia).
      rewrite
      SearchAbout (?x - ?x mod _).
      change (4^k) with ((2^2)^k).
      rewrite <- Z.pow_mul_r by lia.
      replace (2*k) with (k+k) by lia.
      rewrite Z.pow_add_r by lia.
      rewrite !Z.div_div by lia.

      rewrite (Z.mul_comm n).
      rewrite <- !(Z.div_div _ _ n) by lia.


  a - (a - a mod n + (if (a * 4 ^ k / n) mod 4 ^ k <? a then -1 else 0) * n) + 1 <= 2 * n



      break_match; auto with lia.
    Qed.

    (** In that case, we have *)
    Theorem barrett_reduction_small
      : a mod n = if r <? n
                  then r
                  else r - n.
    Proof.
      pose proof r_small. pose proof qn_small.
      destruct (r <? n) eqn:rlt; Z.ltb_to_lt.
      { symmetry; apply (Zmod_unique a n q); subst r; lia. }
      { symmetry; apply (Zmod_unique a n (q + 1)); subst r; lia. }
    Qed.
  End barrett_algorithm.
End barrett.
