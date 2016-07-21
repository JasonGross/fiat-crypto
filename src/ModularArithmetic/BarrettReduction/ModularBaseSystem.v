(*** Barrett Reduction *)
(** This file implements Barrett Reduction on any [BaseVector] which
    is a power-of-two base.  See [BarrettReduction/Z.v] for an
    explanation of the algorithm. *)
Require Import Coq.ZArith.ZArith Coq.micromega.Psatz Coq.Lists.List.
Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.Pow2Base.
Require Import Crypto.ModularArithmetic.ExtendedBaseVector.
Require Import Crypto.Util.ZUtil Crypto.Util.ListUtil.

Local Open Scope Z_scope.

Section barrett.
  Context (limb_widths : list Z)
          (limb_widths_nonnegative : forall x, In x limb_widths -> 0 <= x).
  Local Notation base := (base_from_limb_widths limb_widths).
  Context (n : digits)
          (n_reasonable : BaseSystem.decode base n <> 0)
          (a : digits)
          (a_length : length a = (length limb_widths + length limb_widths)%nat).

  (** * Barrett algorithm *)
  Section barrett_algorithm.
    (** We take [k], an integer such that [2ᵏ > n], to be the width of
        our base. *)
    Local Notation k := (sum_firstn limb_widths (length limb_widths)).
    Context (length_n : length n = length limb_widths)
            (m : digits)
            (m_length : length n = (length limb_widths + length limb_widths)%nat)
            (m_good : BaseSystem.decode (ext_base limb_widths) m
                      = 4^k / BaseSystem.decode base n).

    Let qv := (m * BaseSystem.decode base a) / 4^k.
    Context (q : digits)
            (q_length : length q = length limb_widths + length limb_widths)
            (q_good :
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
      pose proof k_nonnegative; subst q r m.
      assert (0 <= 2^(k-1)) by zero_bounds.
      Z.simplify_fractions_le.
    Qed.

    (** Also, if [a < n²] then [r < 2n]. *)
    (** N.B. It turns out that it is sufficient to assume [a < 4ᵏ]. *)
    Context (a_small : a < 4^k).
    Lemma r_small : r < 2 * n.
    Proof.
      Hint Rewrite (Z.div_small a (4^k)) (Z.mod_small a (4^k)) using lia : zsimplify.
      Hint Rewrite (Z.mul_div_eq' a n) using lia : zstrip_div.
      cut (r + 1 <= 2 * n); [ lia | ].
      pose proof k_nonnegative; subst r q m.
      assert (0 <= 2^(k-1)) by zero_bounds.
      assert (4^k <> 0) by auto with zarith lia.
      assert (a mod n < n) by auto with zarith lia.
      pose proof (Z.mod_pos_bound (a * 4^k / n) (4^k)).
      transitivity (a - (a * 4 ^ k / n - a) / 4 ^ k * n + 1).
      { rewrite <- (Z.mul_comm a); auto 6 with zarith lia. }
      rewrite (Z_div_mod_eq (_ * 4^k / n) (4^k)) by lia.
      autorewrite with push_Zmul push_Zopp zsimplify zstrip_div.
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


Require Import Coq.ZArith.Zpower Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ListUtil Crypto.Util.CaseUtil Crypto.Util.ZUtil.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ExtendedBaseVector.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Util.Notations.
Require Import Crypto.ModularArithmetic.Pow2Base.
Local Open Scope Z_scope.

Section PseudoMersenneBase.
  Context `{prm :PseudoMersenneBaseParams}.

  Definition decode (us : digits) : F modulus := ZToField (BaseSystem.decode base us).

  Definition rep (us : digits) (x : F modulus) := (length us = length base)%nat /\ decode us = x.
  Local Notation "u ~= x" := (rep u x).
  Local Hint Unfold rep.

  (* max must be greater than input; this is used to truncate last digit *)
  Definition encode (x : F modulus) := encodeZ limb_widths x.

  (* Converts from length of extended base to length of base by reduction modulo M.*)
  Definition reduce (us : digits) : digits :=
    let high := skipn (length base) us in
    let low := firstn (length base) us in
    let wrap := map (Z.mul c) high in
    BaseSystem.add low wrap.

  Definition mul (us vs : digits) := reduce (BaseSystem.mul ext_base us vs).

  Definition sub (xs : digits) (xs_0_mod : (BaseSystem.decode base xs) mod modulus = 0) (us vs : digits) :=
      BaseSystem.sub (add xs us) vs.

End PseudoMersenneBase.

Section CarryBasePow2.
  Context `{prm :PseudoMersenneBaseParams}.

  Definition log_cap i := nth_default 0 limb_widths i.

  Definition add_to_nth n (x:Z) xs :=
    set_nth n (x + nth_default 0 xs n) xs.

  Definition pow2_mod n i := Z.land n (Z.ones i).

  Definition carry_simple i := fun us =>
    let di := nth_default 0 us      i in
    let us' := set_nth i (pow2_mod di (log_cap i)) us in
    add_to_nth (S i) (   (Z.shiftr di (log_cap i))) us'.

  Definition carry_and_reduce i := fun us =>
    let di := nth_default 0 us      i in
    let us' := set_nth i (pow2_mod di (log_cap i)) us in
    add_to_nth   0  (c * (Z.shiftr di (log_cap i))) us'.

  Definition carry i : digits -> digits :=
    if eq_nat_dec i (pred (length base))
    then carry_and_reduce i
    else carry_simple i.

  Definition carry_sequence is us := fold_right carry us is.

  Fixpoint make_chain i :=
    match i with
    | O => nil
    | S i' => i' :: make_chain i'
    end.

  Definition full_carry_chain := make_chain (length limb_widths).

  Definition carry_full := carry_sequence full_carry_chain.

  Definition carry_mul us vs := carry_full (mul us vs).

End CarryBasePow2.

Section Canonicalization.
  Context `{prm :PseudoMersenneBaseParams}.

  (* compute at compile time *)
  Definition max_ones := Z.ones (fold_right Z.max 0 limb_widths).

  Definition max_bound i := Z.ones (log_cap i).

  Fixpoint isFull' us full i :=
    match i with
    | O => andb (Z.ltb (max_bound 0 - c) (nth_default 0 us 0)) full
    | S i' => isFull' us (andb (Z.eqb (max_bound i) (nth_default 0 us i)) full) i'
    end.

  Definition isFull us := isFull' us true (length base - 1)%nat.

  Fixpoint modulus_digits' i :=
    match i with
    | O => max_bound i - c + 1 :: nil
    | S i' => modulus_digits' i' ++ max_bound i :: nil
    end.

  (* compute at compile time *)
  Definition modulus_digits := modulus_digits' (length base - 1).

  Definition and_term us := if isFull us then max_ones else 0.

  Definition freeze us :=
    let us' := carry_full (carry_full (carry_full us)) in
    let and_term := and_term us' in
    (* [and_term] is all ones if us' is full, so the subtractions subtract q overall.
       Otherwise, it's all zeroes, and the subtractions do nothing. *)
     map2 (fun x y => x - y) us' (map (Z.land and_term) modulus_digits).

End Canonicalization.
