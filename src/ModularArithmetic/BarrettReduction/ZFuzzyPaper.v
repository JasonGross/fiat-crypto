(*** Barrett Reduction *)
(** This file implements a slightly-generalized version of Barrett Reduction on [Z]. *)
Require Import Coq.ZArith.ZArith Coq.micromega.Psatz.
Require Import Crypto.Util.ZUtil Crypto.Util.Tactics Crypto.Algebra.

Local Open Scope Z_scope.

Section barrett.
  (** Quoting the Handbook of Applied Cryptography <http://cacr.uwaterloo.ca/hac/about/chap14.pdf>: *)
  (** Barrett reduction (Algorithm 14.42) computes [r = x mod m] given
      [x] and [m]. The algorithm requires the precomputation of the
      quantity [µ = ⌊b²ᵏ/m⌋]; it is advantageous if many reductions
      are performed with a single modulus. For example, each RSA
      encryption for one entity requires reduction modulo that
      entity’s public key modulus. The precomputation takes a fixed
      amount of work, which is negligible in comparison to modular
      exponentiation cost.  Typically, the radix [b] is chosen to be
      close to the word-size of the processor. Hence, assume [b > 3] in
      Algorithm 14.42 (see Note 14.44 (ii)). *)

  (** * Barrett modular reduction *)
  Section barrett_modular_reduction.
    Context (m b x k μ offset : Z)
            (m_reasonable : m <> 0)
            (base_reasonable : 0 < b)
            (k_good : m < b^k)
            (μ_good : μ = b^(2*k) / m) (* [/] is [Z.div], which is truncated *)
            (x_nonneg : 0 <= x)
            (offset_nonneg : 0 <= offset).
    (** N.B. We generalize to [k ± offset] from [k ± 1]. *)
    (** INPUT: positive integers [x = (x₂ₖ₋₁···x₁x₀)_b], [m =
        (mₖ₋₁···m₁m₀)_b] (with [mₖ₋₁ ≠ 0]), and [µ = ⌊b²ᵏ/m⌋. *)
    (** OUTPUT: [r = x mod m] *)
    (** 1. [q₁ ← ⌊x/bᵏ⁻¹⌋], [q₂ ← q₁ · µ], [q₃ ← ⌊q₂/bᵏ⁺¹⌋].
        2. [r₁ ← x mod bᵏ⁺¹], [r₂ ← q₃ · m mod bk+1, r←r1 − r2.
3. If r < 0 then r←r + bk+1.
4. While r ≥ m do: r←r − m.
5. Return(r).
>> *)
    (** Barrett algorithm is a fixed-point analog which expresses
        everything in terms of integers. Let [k] be the smallest
        integer such that [2ᵏ > n]. Think of [n] as representing the
        fixed-point number [n 2⁻ᵏ]. We precompute [m] such that [m =
        ⌊4ᵏ / n⌋]. Then [m] represents the fixed-point number
        [m 2⁻ᵏ ≈ (n 2⁻ᵏ)⁻¹]. *)
    (** N.B. We don't need [k] to be the smallest such integer. *)
    (** N.B. We generalize to an arbitrary base. *)
    (** N.B. We generalize from [k ± 1] to [k ± offset]. *)
    Context (b : Z)
            (base_good : 0 < b)
            (k : Z)
            (k_good : n < b ^ k)
            (m : Z)
            (m_good : m = b^(2*k) / n).
    (** Wikipedia neglects to mention non-negativity, but we need it.
        It might be possible to do with a relaxed assumption, such as
        the sign of [a] and the sign of [n] being the same; but I
        figured it wasn't worth it. *)
    Context (n_pos : 0 < n) (* or just [0 <= n], since we have [n <> 0] above *)
            (a_nonneg : 0 <= a).

    Context (k_big_enough : offset <= k).

    (** Now *)

    Let q := (m * (a / b^(k-offset))) / b^(k+offset).
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
      subst q r m.
      assert (0 < b^(k-offset)). zero_bounds.
      assert (0 < b^(k+offset)) by zero_bounds.
      assert (0 < b^(2 * k)) by zero_bounds.
      Z.simplify_fractions_le.
      autorewrite with pull_Zpow pull_Zdiv zsimplify; reflexivity.
    Qed.

    (** Also, if [a < n²] then [r < 2n]. *)
    (** N.B. It turns out that it is sufficient to assume [a < b²ᵏ]. *)
    Context (a_small : a < b^(2*k)).
    (** We also need that [n] is large enough; [n] larger than bᵏ⁻¹
        works, but we ask for something more precise. *)
    Context (n_large : a mod b^(k-offset) <= n).
    Lemma q_nice : { b : bool * bool | q = a / n + (if fst b then -1 else 0) + (if snd b then -1 else 0) }.
    Proof.
      assert (0 < b^(k+offset)) by zero_bounds.
      assert (0 < b^(k-offset)) by zero_bounds.
      assert (a / b^(k-offset) <= b^(2*k) / b^(k-offset)) by auto with zarith lia.
      assert (a / b^(k-offset) <= b^(k+offset)) by (autorewrite with pull_Zpow zsimplify in *; assumption).
      subst q r m.
      rewrite (Z.div_mul_diff_exact''' (b^(2*k)) n (a/b^(k-offset))) by auto with lia zero_bounds.
      rewrite (Z_div_mod_eq (b^(2*k) * _ / n) (b^(k+offset))) by lia.
      autorewrite with push_Zmul push_Zopp zsimplify zstrip_div zdiv_to_mod.
      rewrite Z.div_sub_mod_cond, !Z.div_sub_small by auto with zero_bounds zarith.
      eexists (_, _); reflexivity.
    Qed.

    Lemma r_small : r < 3 * n.
    Proof.
      Hint Rewrite (Z.mul_div_eq' a n) using lia : zstrip_div.
      assert (a mod n < n) by auto with zarith lia.
      subst r; rewrite (proj2_sig q_nice); generalize (proj1_sig q_nice); intro; subst q m.
      autorewrite with push_Zmul zsimplify zstrip_div.
      break_match; auto with lia.
    Qed.

    (** In that case, we have *)
    Theorem barrett_reduction_small
      : a mod n = if r <? n
                  then r
                  else if r <? 2 * n
                       then r - n
                       else r - 2 * n.
    Proof.
      pose proof r_small. pose proof qn_small.
      destruct (r <? n) eqn:?, (r <? 2 * n) eqn:?; Z.ltb_to_lt; try lia.
      { symmetry; apply (Zmod_unique a n q); subst r; lia. }
      { symmetry; apply (Zmod_unique a n (q + 1)); subst r; lia. }
      { symmetry; apply (Zmod_unique a n (q + 2)); subst r; lia. }
    Qed.
  End barrett_algorithm.
End barrett.
