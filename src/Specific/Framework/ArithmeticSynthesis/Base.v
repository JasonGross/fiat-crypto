Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.micromega.Lia.
Require Import Coq.QArith.QArith_base.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.HelperTactics.
Require Import Crypto.Util.QUtil.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.ReplaceNegWithPos.
Require Import Crypto.Util.ZUtil.ModInv.
Require Import Crypto.Util.SideConditions.CorePackages.
Require Import Crypto.Util.SideConditions.ModInvPackage.
Require Import Crypto.Util.SideConditions.ReductionPackages.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Decidable.Decidable2Bool.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Bool.
Require Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.CacheTerm.

Local Set Implicit Arguments.

Local Existing Instance Tuple.dec_fieldwise.

  (* emacs for adjusting definitions *)
  (* Query replace regexp (default Definition \([a-zA-Z_0-9]+\) : \([A-Za-z0-9_]+\) := P.compute \(.*\)\.\(.*\) -> Ltac pose_\1 \1 :=\4^J  cache_term_with_type_by^J      \2^J      ltac:(let v := P.do_compute \3 in exact v)^J      \1.):  *)
  (* Query replace regexp (default Definition \([a-zA-Z_0-9]+\) : \([A-Za-z0-9_]+\) := P.compute \(.*\)\.\(.*\) -> Ltac pose_\1 \1 :=\4^J  cache_term_with_type_by^J      \2^J      ltac:(let v := P.do_compute \3 in exact v)^J      \1.):  *)
  (* Query replace regexp (default Definition \([a-zA-Z_0-9]+\) : \([A-Za-z0-9_ \.]*\) := P.compute \(.*\)\.\(.*\) -> Ltac pose_\1 \1 :=\4^J  cache_term_with_type_by^J      (\2)^J      ltac:(let v := P.do_compute \3 in exact v)^J      \1.): *)
  (* Query replace regexp (default Definition \([a-zA-Z_0-9]+\) := P.compute \(.*\)\.\(.*\) -> Ltac pose_\1 \1 :=\3^J  let v := P.do_compute \2 in cache_term v \1.):  *)

Section wt.
  Import QArith Qround.
  Local Coercion QArith_base.inject_Z : Z >-> Q.
  Local Coercion Z.of_nat : nat >-> Z.
  Local Coercion Z.pos : positive >-> Z.
  Definition lgwt_gen (base : Q) (i:nat) : Z := Qceiling (base * i).
  Definition wt_gen (base : Q) (i:nat) : Z := 2^lgwt_gen base i.
End wt.

Section gen.
  Context (base : Q)
          (m : positive)
          (sz : nat)
          (coef_div_modulus : nat)
          (base_pos : (1 <= base)%Q).

  Local Notation wt := (wt_gen base).

  Definition sz2' := ((sz * 2) - 1)%nat.

  Definition half_sz' := (sz / 2)%nat.

  Definition m_enc'
    := Positional.encode (modulo_cps:=@modulo_cps) (div_cps:=@div_cps) (n:=sz) wt (Z.pos m).

  Definition m_enc_minus_1'
    := Positional.encode (modulo_cps:=@modulo_cps) (div_cps:=@div_cps) (n:=sz) wt (Z.pos m - 1).

  Lemma sz2'_nonzero
        (sz_nonzero : sz <> 0%nat)
    : sz2' <> 0%nat.
  Proof using Type. clear -sz_nonzero; cbv [sz2']; omega. Qed.

  Local Ltac Q_cbv :=
    cbv [wt_gen lgwt_gen Qround.Qceiling QArith_base.Qmult QArith_base.Qdiv QArith_base.inject_Z QArith_base.Qden QArith_base.Qnum QArith_base.Qopp Qround.Qfloor QArith_base.Qinv QArith_base.Qle QArith_base.Qeq Z.of_nat] in *.
  Lemma wt_gen0_1 : wt 0 = 1.
  Proof using Type.
    Q_cbv; simpl.
    autorewrite with zsimplify_const; reflexivity.
  Qed.

  Lemma wt_gen_nonzero : forall i, wt i <> 0.
  Proof using base_pos.
    eapply pow_ceil_mul_nat_nonzero; [ omega | ].
    destruct base; Q_cbv; lia.
  Qed.

  Lemma wt_gen_nonneg : forall i, 0 <= wt i.
  Proof using Type. apply pow_ceil_mul_nat_nonneg; omega. Qed.

  Lemma wt_gen_pos : forall i, wt i > 0.
  Proof using base_pos.
    intro i; pose proof (wt_gen_nonzero i); pose proof (wt_gen_nonneg i).
    omega.
  Qed.

  Lemma wt_gen_multiples : forall i, wt (S i) mod (wt i) = 0.
  Proof using base_pos.
    apply pow_ceil_mul_nat_multiples; destruct base; Q_cbv; lia.
  Qed.

  Section divides.
    Lemma wt_gen_divides
      : forall i, wt (S i) / wt i > 0.
    Proof using base_pos.
      apply pow_ceil_mul_nat_divide; [ omega | ].
      destruct base; Q_cbv; lia.
    Qed.

    Lemma wt_gen_divides'
      : forall i, wt (S i) / wt i <> 0.
    Proof using base_pos.
      symmetry; apply Z.lt_neq, Z.gt_lt_iff, wt_gen_divides; assumption.
    Qed.

    Lemma wt_gen_div_bound
      : forall i, wt (S i) / wt i <= wt 1.
    Proof using base_pos.
      intro; etransitivity.
      eapply pow_ceil_mul_nat_divide_upperbound; [ omega | ].
      all:destruct base; Q_cbv; autorewrite with zsimplify_const;
        rewrite ?Pos.mul_1_l, ?Pos.mul_1_r; try assumption; omega.
    Qed.
    Lemma wt_gen_divides_chain
          carry_chain
      : forall i (H:In i carry_chain), wt (S i) / wt i <> 0.
    Proof using base_pos. intros i ?; apply wt_gen_divides'; assumption. Qed.

    Lemma wt_gen_divides_chains
          carry_chains
      : List.fold_right
          and
          True
          (List.map
             (fun carry_chain
              => forall i (H:In i carry_chain), wt (S i) / wt i <> 0)
             carry_chains).
    Proof using base_pos.
      induction carry_chains as [|carry_chain carry_chains IHcarry_chains];
        constructor; eauto using wt_gen_divides_chain.
    Qed.
  End divides.

  Definition coef'
    := (fix addm (acc: Z^sz) (ctr : nat) : Z^sz :=
          match ctr with
          | O => acc
          | S n => addm (Positional.add_cps wt acc m_enc' id) n
          end) (Positional.zeros sz) coef_div_modulus.

  Lemma coef_mod'
    : mod_eq m (Positional.eval (n:=sz) wt coef') 0.
  Proof using base_pos.
    cbv [coef' m_enc'].
    remember (Positional.zeros sz) as v eqn:Hv.
    assert (Hv' : mod_eq m (Positional.eval wt v) 0)
      by (subst v; autorewrite with push_basesystem_eval; reflexivity);
      clear Hv.
    revert dependent v.
    induction coef_div_modulus as [|n IHn]; clear coef_div_modulus;
      intros; [ assumption | ].
    rewrite IHn; [ reflexivity | ].
    pose proof wt_gen0_1.
    pose proof wt_gen_nonzero.
    pose proof div_mod.
    pose proof wt_gen_divides'.
    destruct (Nat.eq_dec sz 0).
    { subst; reflexivity. }
    { repeat autounfold; autorewrite with uncps push_id push_basesystem_eval.
      rewrite Positional.eval_encode by (intros; autorewrite with uncps; unfold id; auto).
      cbv [mod_eq] in *.
      push_Zmod; rewrite Hv'; pull_Zmod.
      reflexivity. }
  Qed.

  Definition bounds_exponents' :=
    Tuple.map (fun i => Z.log2 (wt (S i) / wt i))
              (Tuple.from_list sz (seq 0 sz) (seq_length _ _)).
  Local Notation b_of upper_bound_of_exponent
    := (fun exp => {| lower := 0 ; upper := upper_bound_of_exponent exp |}%Z).
  Definition bounds' upper_bound_of_exponent
    := Tuple.map (b_of upper_bound_of_exponent) bounds_exponents'.

  Lemma relax'_pf {in_bounds out_bounds} {v : Z^sz}
        (Htight : Tuple.fieldwiseb is_tighter_than_bool in_bounds out_bounds = true)
    : is_bounded_by None in_bounds v -> is_bounded_by None out_bounds v.
  Proof.
    destruct sz as [|sz']; simpl in *; trivial.
    induction sz' as [|sz' IHsz]; simpl in *;
      repeat first [ exact I
                   | progress destruct_head'_prod
                   | progress destruct_head' zrange
                   | progress cbv [is_tighter_than_bool] in *
                   | progress split_andb
                   | progress Z.ltb_to_lt
                   | progress cbn [fst snd ZRange.lower ZRange.upper] in *
                   | progress destruct_head_hnf' and
                   | progress intros
                   | apply conj
                   | omega
                   | solve [ eauto ] ].
  Qed.

  Lemma relax_bounds'_precise
        {upper_bound_of_exponent_in upper_bound_of_exponent_out}
        {v : Z^sz}
        (Htight : forall x : nat,
            (x < sz)%nat
            -> upper_bound_of_exponent_in (Z.log2 (wt (S x) / wt x)) <=
               upper_bound_of_exponent_out (Z.log2 (wt (S x) / wt x)))
    : is_bounded_by None (bounds' upper_bound_of_exponent_in) v
      -> is_bounded_by None (bounds' upper_bound_of_exponent_out) v.
  Proof.
    apply relax'_pf; cbv [bounds' bounds_exponents'].
    rewrite !Tuple.map_map; cbn.
    rewrite Tuple.fieldwiseb_fieldwise, Tuple.fieldwise_map_from_list_iff, Forall_forall
      by (intros; apply reflexivity);
      intro x; rewrite ListUtil.List.in_seq; intro Hlt.
    cbn; Z.ltb_to_lt.
    intuition.
  Qed.

  Lemma relax_bounds'_computational
        {upper_bound_of_exponent_in upper_bound_of_exponent_out}
        {v : Z^sz}
        (Htight
         : (if
               dec
                 (Forall
                    (fun x : nat =>
                       (upper_bound_of_exponent_in (Z.log2 (wt (S x) / wt x)) <=?
                        upper_bound_of_exponent_out (Z.log2 (wt (S x) / wt x))) = true)
                    (seq 0 sz))
             then true
             else false) = true)
    : is_bounded_by None (bounds' upper_bound_of_exponent_in) v
      -> is_bounded_by None (bounds' upper_bound_of_exponent_out) v.
  Proof.
    apply relax'_pf; cbv [bounds' bounds_exponents'].
    rewrite !Tuple.map_map; cbn.
    rewrite Tuple.fieldwiseb_fieldwise, Tuple.fieldwise_map_from_list_iff
      by (intros; apply reflexivity).
    cbn.
    apply dec_bool; assumption.
  Qed.

  Lemma relax_bounds'
        {upper_bound_of_exponent_in upper_bound_of_exponent_out}
        {v : Z^sz}
        (Htight : forall x,
            0 <= x
            -> upper_bound_of_exponent_in x <=
               upper_bound_of_exponent_out x)
    : is_bounded_by None (bounds' upper_bound_of_exponent_in) v
      -> is_bounded_by None (bounds' upper_bound_of_exponent_out) v.
  Proof.
    apply relax_bounds'_precise.
    intros x ?; apply Htight, Z.log2_nonneg.
  Qed.

  Lemma feBW_bounded_helper'
        (wt : nat -> Z)
        (Hwt : forall i, 0 <= wt i)
        (bounds : zrange^sz)
    : forall a,
      is_bounded_by None bounds a
      -> B.Positional.eval wt (Tuple.map lower bounds)
         <= B.Positional.eval wt a
         <= B.Positional.eval wt (Tuple.map upper bounds).
  Proof.
    intro a; revert dependent wt.
    destruct sz as [|sz'].
    { intros wt H; cbv -[Z.le Z.lt Z.mul]; lia. }
    { cbn [Tuple.tuple Tuple.map] in *.
      induction sz' as [|sz' IHsz]; intros wt Hwt H.
      { cbv -[Z.le Z.lt upper lower Z.mul Z.pow Z.add Nat.log2 Z.log2 Z.div] in H |- *.
        repeat match goal with
               | [ H : forall j, 0 <= wt j |- context[wt ?i] ]
                 => pose proof (H i); generalize dependent (wt i); intros
               end.
        nia. }
      { pose proof (Hwt 0%nat).
        cbn [Tuple.tuple' Tuple.map'] in *.
        destruct a as [a' a], bounds as [bounds b], H as [H [H' _]].
        cbn [fst snd] in *.
        setoid_rewrite (@B.Positional.eval_step (S _)).
        specialize (IHsz bounds a' (fun i => wt (S i)) (fun i => Hwt _) H).
        nia. } }
  Qed.

  Lemma feBW_bounded_helper_gen_wt
        (wt : nat -> Z)
        (Hwt : forall i, 0 <= wt i)
        (bounds : zrange^sz)
        l u
    : l <= B.Positional.eval wt (Tuple.map lower bounds)
      /\ B.Positional.eval wt (Tuple.map upper bounds) < u
      -> forall a,
        is_bounded_by None bounds a
        -> l <= B.Positional.eval wt a < u.
  Proof.
    intros [Hl Hu] a; split;
      [ eapply Z.le_trans | eapply Z.le_lt_trans ];
      [ | eapply feBW_bounded_helper' | eapply feBW_bounded_helper' | ];
      eassumption.
  Qed.

  Lemma feBW_bounded_helper
        upper_bound_of_exponent
        (bounds := bounds' upper_bound_of_exponent)
        u
    : B.Positional.eval wt (Tuple.map upper bounds) < u
      -> forall a,
        is_bounded_by None bounds a
        -> 0 <= B.Positional.eval wt a < u.
  Proof.
    intro H; apply feBW_bounded_helper_gen_wt; [ apply wt_gen_nonneg | ].
    split; [ | assumption ].
    subst bounds; cbv [bounds' bounds_exponents'].
    rewrite !Tuple.map_map; cbn; apply Z.eq_le_incl.
    symmetry; etransitivity; [ | apply Positional.eval_zeros ].
    f_equal.
    erewrite <- Positional.map_and_0.
    erewrite <- (Tuple.map_map (fun _ => 0) Z.of_nat).
    apply Tuple.map_Proper.
    { symmetry; exact Z.land_0_l. }
    { reflexivity. }
  Qed.
End gen.

Section with_curve_parameters.
  Context (curve : CurveParameters.CurveParameters).

  Local Notation bitwidth := curve.(bitwidth).
  Local Notation s := curve.(s).
  Local Notation c := curve.(c).
  Local Notation base := curve.(base).
  Local Notation sz := curve.(sz).
  Local Notation coef_div_modulus := curve.(coef_div_modulus).
  Local Notation carry_chains := curve.(carry_chains).
  Local Notation modinv_fuel := curve.(modinv_fuel).

  Definition r := Z.to_pos (2^bitwidth).
  Definition m (* modulus *) := Z.to_pos (s - Associational.eval c).
  Definition lgwt := Eval cbv [lgwt_gen CurveParameters.base Qround.Qceiling Qround.Qfloor Qdiv inject_Z Qopp Qmult Qden Qnum] in lgwt_gen base.
  Definition wt := Eval cbv [lgwt_gen wt_gen CurveParameters.base Qround.Qceiling Qround.Qfloor Qdiv inject_Z Qopp Qmult Qden Qnum] in wt_gen base.
  Definition sz2 := sz2' sz.
  Definition half_sz := half_sz' sz.
  Definition m_enc := m_enc' base m sz.
  Definition m_enc_minus_1 := m_enc_minus_1' base m sz.
  Definition coef := coef' base m sz coef_div_modulus.
  Definition sqrt_s := 2^(Z.log2 s / 2).
  Definition bounds_exponents : Z^sz := bounds_exponents' base sz.
  Definition bounds_tight : zrange^sz
    := bounds' base sz curve.(upper_bound_of_exponent_tight).
  Definition bounds_loose : zrange^sz
    := bounds' base sz curve.(upper_bound_of_exponent_loose).
  Definition bounds_limb_widths : zrange^sz
    := bounds' base sz (fun e => 2^e - 1).
  Definition bounds_bitwidths : zrange^sz
    := bounds' base sz (fun e => 2^bitwidth - 1).
  Definition bound1 := {| lower := 0 ; upper := Z.pos r-1 |}.

  Record CurveParameterBaseSideConditions :=
    { s_nonzero' : vm_decide_package _;
      s_nonzero : s <> 0 := dec_bool s_nonzero';
      sz_le_log2_m' : vm_decide_package _;
      sz_le_log2_m : Z.of_nat sz <= Z.log2_up (Z.pos m) := dec_bool sz_le_log2_m';
      base_pos' : vm_decide_package _;
      base_pos : (1 <= base)%Q := dec_bool base_pos';
      m_correct' : vm_decide_package _;
      m_correct : Z.pos m = s - Associational.eval c := dec_bool m_correct';
      m_correct_wt' : vm_decide_package _;
      m_correct_wt : if curve.(freeze) then Z.pos m = wt sz - Associational.eval c else True
      := dec_bool m_correct_wt';
      m_enc_correct' : vm_decide_package _;
      m_enc_correct : if curve.(freeze) then Positional.eval wt m_enc = Z.pos m else True
      := dec_bool m_enc_correct';
      m_enc_minus_1_correct' : vm_decide_package _;
      m_enc_minus_1_correct : Positional.eval wt m_enc_minus_1 = Z.pos m - 1
      := dec_bool m_enc_minus_1_correct';
      half_sz_nonzero' : vm_decide_package _;
      half_sz_nonzero : if orb curve.(goldilocks) curve.(karatsuba) then half_sz <> 0%nat else True
      := dec_bool half_sz_nonzero';
      sqrt_s_nonzero' : vm_decide_package _;
      sqrt_s_nonzero : if orb curve.(goldilocks) curve.(karatsuba) then sqrt_s <> 0 else True
      := dec_bool sqrt_s_nonzero';
      fst_nat_divmod_sz_nonzero' : vm_decide_package _;
      fst_nat_divmod_sz_nonzero : if orb curve.(goldilocks) curve.(karatsuba) then fst (Nat.divmod sz 1 0 1) <> 0%nat else True
      := dec_bool fst_nat_divmod_sz_nonzero';
      sqrt_s_correct' : vm_decide_package _;
      sqrt_s_correct : if curve.(goldilocks) then mod_eq m (sqrt_s ^ 2) (sqrt_s + 1) else True
      := dec_bool sqrt_s_correct';
      coef_mod : mod_eq m (Positional.eval (n:=sz) wt coef) 0
      := @coef_mod' _ _ _ _ base_pos;
      sz_nonzero' : vm_decide_package _;
      sz_nonzero : sz <> 0%nat := dec_bool sz_nonzero';
      sz2_nonzero : sz2 <> 0%nat := sz2'_nonzero sz_nonzero;
      wt_nonzero : forall i, wt i <> 0
      := @wt_gen_nonzero _ base_pos;
      wt_nonneg : forall i, 0 <= wt i
      := wt_gen_nonneg _;
      wt_pos : forall i, wt i > 0
      := @wt_gen_pos _ base_pos;
      wt0_1 : wt 0 = 1
      := @wt_gen0_1 _;
      wt_div_bound : forall i, wt (S i) / wt i <= wt 1
      := wt_gen_div_bound base_pos;
      wt_divides : forall i, wt (S i) / wt i > 0
      := @wt_gen_divides _ base_pos;
      wt_divides' : forall i, wt (S i) / wt i <> 0
      := @wt_gen_divides' _ base_pos;
      wt_divides_chains
      : List.fold_right
          and
          True
          (List.map
             (fun carry_chain
              => forall i (H:In i carry_chain), wt (S i) / wt i <> 0)
             carry_chains)
      := @wt_gen_divides_chains _ base_pos carry_chains;
      wt_multiples : forall i, wt (S i) mod (wt i) = 0
      := @wt_gen_multiples _ base_pos;
      c_small' : vm_decide_package _;
      c_small : 0 < Associational.eval c < wt sz := dec_bool c_small';
      base_le_bitwidth' : cbv_minus_then_vm_decide_package Z.le _; (* this is purely a sanity check *)
      base_le_bitwidth : (base <= inject_Z bitwidth)%Q := dec_bool base_le_bitwidth';
      m_enc_bounded' : vm_compute_reflexivity_package _;
      m_enc_bounded : Tuple.map (n:=sz) (BinInt.Z.land (Z.ones bitwidth)) m_enc = m_enc
      := dec_bool m_enc_bounded';
      m_enc_minus_1_bounded_fieldwise' : vm_decide_package _;
      m_enc_minus_1_bounded_fieldwise
      : Tuple.fieldwise
          (fun x y => 0 <= y < 2 ^ Z.log2 (wt (S x) / wt x))
          (Tuple.from_list sz (seq 0 sz) (seq_length sz 0))
          m_enc_minus_1
      := dec_bool m_enc_minus_1_bounded_fieldwise';
      tight_bounds_tigher' : vm_decide_package _;
      tight_bounds_tigher
      : (if
            dec
              (Forall
                 (fun x : nat =>
                    (curve.(upper_bound_of_exponent_tight)
                             (Z.log2 (wt (S x) / wt x))
                     <=? curve.(upper_bound_of_exponent_loose)
                                 (Z.log2 (wt (S x) / wt x))) = true)
                 (seq 0 sz))
          then true
          else false) = true
      := tight_bounds_tigher';
      bitwidth_bounds_loosest' : vm_decide_package _;
      bitwidth_bounds_loosest
      : (if
            dec
              (Forall
                 (fun x : nat =>
                    (curve.(upper_bound_of_exponent_loose)
                             (Z.log2 (wt (S x) / wt x))
                     <=? 2^bitwidth - 1) = true)
                 (seq 0 sz))
          then true
          else false) = true
      := bitwidth_bounds_loosest';
      limb_width_bounds_tightest' : vm_decide_package _;
      limb_width_bounds_tightest
      : (if
            dec
              (Forall
                 (fun x : nat =>
                    (2^(Z.log2 (wt (S x) / wt x)) - 1
                     <=? curve.(upper_bound_of_exponent_tight)
                                 (Z.log2 (wt (S x) / wt x))) = true)
                 (seq 0 sz))
          then true
          else false) = true
      := limb_width_bounds_tightest';
      tight_bounds_lt_2m' : vm_decide_package _;
      tight_bounds_lt_2m
      : B.Positional.eval wt (Tuple.map upper bounds_tight) < 2 * Z.pos m
      := dec_bool tight_bounds_lt_2m';
    }.

  Hint Unfold mod_eq : dec2bool.

  Local Ltac precheck R :=
    lazymatch R with
    | curve.(freeze) => idtac
    | curve.(karatsuba) => idtac
    | curve.(goldilocks) => idtac
    end.

  Definition CurveParameterBaseSideConditions_fast'
    : { b : bool | b = true -> CurveParameterBaseSideConditions }.
  Proof. make_parameter_package_for_vm_decide precheck. Defined.

  Definition CurveParameterBaseSideConditions_bool
    := Eval cbv [CurveParameterBaseSideConditions_fast' proj1_sig] in
        proj1_sig CurveParameterBaseSideConditions_fast'.

  Lemma CurveParameterBaseSideConditions_bool_correct
    : CurveParameterBaseSideConditions_bool = true
      -> CurveParameterBaseSideConditions.
  Proof. exact (proj2_sig CurveParameterBaseSideConditions_fast'). Qed.

  Context (curve_sc : CurveParameterBaseSideConditions).

  Lemma bitwidth_pos : 1 <= bitwidth.
  Proof.
    pose proof (QArith_base.Qle_trans _ _ _ curve_sc.(base_pos) curve_sc.(base_le_bitwidth)) as H.
    cbv [QArith_base.inject_Z QArith_base.Qle QArith_base.Qnum QArith_base.Qden] in H.
    omega.
  Qed.

  Lemma relax_bounds
        {v : Z^sz}
    : is_bounded_by None bounds_tight v
      -> is_bounded_by None bounds_loose v.
  Proof.
    apply relax_bounds'_computational, curve_sc.(tight_bounds_tigher).
  Qed.

  Lemma relax_limb_width_bounds
        {v : Z^sz}
    : is_bounded_by None bounds_limb_widths v
      -> is_bounded_by None bounds_tight v.
  Proof.
    apply relax_bounds'_computational, curve_sc.(limb_width_bounds_tightest).
  Qed.

  Lemma relax_to_bitwidth_bounds
        {v : Z^sz}
    : is_bounded_by None bounds_loose v
      -> is_bounded_by None bounds_bitwidths v.
  Proof.
    apply relax_bounds'_computational, curve_sc.(bitwidth_bounds_loosest).
  Qed.

  Lemma eval_bounded_tight
    : forall a,
      is_bounded_by None bounds_tight a
      -> 0 <= B.Positional.eval wt a < 2 * Z.pos m.
  Proof.
    apply feBW_bounded_helper, curve_sc.(tight_bounds_lt_2m).
  Qed.
End with_curve_parameters.
