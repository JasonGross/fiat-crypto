Require Import Coq.omega.Omega.
Require Import Coq.micromega.Lia.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Tuple.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
Require Import Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Specific.Framework.OutputType.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.ZUtil.Tactics.PeelLe.
Require Import Crypto.Util.ZUtil.Tactics.ReplaceNegWithPos.
Require Import Crypto.Util.Notations.
Import CurveParameters.Notations.

Local Set Implicit Arguments.
Local Coercion Z.to_nat : Z >-> nat.
Local Notation interp_flat_type := (interp_flat_type interp_base_type).

Section gen.
  Context (curve : CurveParameters.CurveParameters)
          (curve_sc : CurveParameterBaseSideConditions curve).

  Local Notation wt := curve.(wt).
  Local Notation m := curve.(m).
  Local Notation sz := curve.(sz).
  Local Notation bitwidth := curve.(bitwidth).

  Local Notation bounds_tight := curve.(bounds_tight).
  Local Notation bounds_loose := curve.(bounds_loose).
  Local Notation bounds_limb_widths := curve.(bounds_limb_widths).
  Local Notation bound1 := curve.(bound1).

  Local Notation TW := (TWord (Z.log2_up bitwidth)).

  Lemma encodeTuple_correct b v
    : flat_interp_tuple (Interp (curve.(encodeTuple) b v) tt)
      = Tuple.map (@cast_const TZ _) v.
  Proof.
    cbv [encodeTuple Interp interp RT rT].
    cbn; rewrite interpf_SmartPairf, SmartVarfMap_tuple.
    cbv [tuple_map].
    rewrite !flat_interp_tuple_untuple, !Tuple.map_map.
    reflexivity.
  Qed.

  Lemma decode_encodeTuple_correct b v
    : curve.(decodeToTuple) b (Interp (curve.(encodeTuple) b v) tt)
      = Tuple.map (n:=sz)
                  (fun x : Z =>
                     match b with
                     | TZ => x
                     | TWord lgsz => Z.max 0 x mod 2 ^ Z.of_nat (PeanoNat.Nat.pow 2 lgsz)
                     end) v.
  Proof.
    cbv [decodeToTuple]; rewrite encodeTuple_correct, Tuple.map_map.
    cbn; setoid_rewrite interpToZ_ZToInterp_mod.
    reflexivity.
  Qed.

  Lemma FdecodeTuple_FencodeTuple
    : forall v, curve.(FdecodeTuple) (curve.(FencodeTuple) v) = v.
  Proof.
    apply Positional.Fdecode_Fencode_id with (modulo_cps:=@modulo_cps) (div_cps:=@div_cps);
      eauto using div_mod, modulo_id, div_id, curve_sc.(wt_nonzero), curve_sc.(wt_divides'), curve_sc.(sz_nonzero), curve_sc.(wt0_1).
  Qed.

  Lemma encode_correct_helper b
        (H : forall v,
            Tuple.map (n:=sz)
                      (fun x : Z =>
                         match b with
                         | TZ => x
                         | TWord lgsz => Z.max 0 x mod 2 ^ Z.of_nat (PeanoNat.Nat.pow 2 lgsz)
                         end) (Positional.Fencode (modulo_cps:=@modulo_cps) (div_cps:=@div_cps) wt v)
            = Positional.Fencode (m:=m) (modulo_cps:=@modulo_cps) (div_cps:=@div_cps) wt v)
    : forall v, curve.(decodeRaw) b (Interp (curve.(encodeRaw) b v) tt) = v.
  Proof.
    cbv [decodeRaw encodeRaw FdecodeTuple FencodeTuple]; intro v.
    rewrite decode_encodeTuple_correct, H; apply FdecodeTuple_FencodeTuple.
  Qed.

  Lemma encodeZ_correct
    : forall v, curve.(decodeRaw) TZ (Interp (curve.(encodeRaw) TZ v) tt) = v.
  Proof.
    apply encode_correct_helper; intro; rewrite Tuple.map_id; reflexivity.
  Qed.

  (* TODO: automate this proof more *)
  Lemma encodeW_correct_helper (b:=TW)
        v
        (encodeV := Positional.Fencode (m:=m) (modulo_cps:=@modulo_cps) (div_cps:=@div_cps) wt v)
        (H_helper : Tuple.map (fun x : Z => Z.max 0 x mod wt 1)
                              encodeV
                    = encodeV)
    : Tuple.map (n:=sz)
                (fun x : Z =>
                   match b with
                   | TZ => x
                   | TWord lgsz => Z.max 0 x mod 2 ^ Z.of_nat (PeanoNat.Nat.pow 2 lgsz)
                   end)
                encodeV
      = encodeV.
  Proof.
    pose proof curve_sc.(base_le_bitwidth) as H.
    pose proof curve_sc.(wt_nonzero) as Hwtnz.
    pose proof curve_sc.(wt_nonneg) as Hwtnn.
    pose proof curve_sc.(wt_div_bound) as Hwt_good.
    subst b.
    match goal with
      [ |- Tuple.map _ ?t = ?rhs ] => cut (Tuple.map (fun x => Z.max 0 x mod (wt 1)) t = rhs);
                                        [ generalize t | ]
    end.
    { clear -H Hwtnz Hwtnn; intros t H'.
      etransitivity; [ | apply Tuple.map_id ].
      pose proof (eq_trans H' (eq_sym (Tuple.map_id _))) as H''; clear H'; revert H''.
      match goal with
      | [ |- ?A -> ?B ] => cut (A /\ Tuple.fieldwise eq t t -> B /\ Tuple.fieldwise eq t t)
      end;
        [ intros P H'; apply P; split; auto; reflexivity | ].
      rewrite <- !Tuple.fieldwise_eq_iff, !Tuple.fieldwise_map_iff.
      rewrite !Tuple.fieldwise_lift_and.
      apply Tuple.fieldwise_Proper; [ | reflexivity.. ]; intros a a' [H' ?]; revert H'; subst a'; intro H'.
      split; [ | reflexivity ].
      destruct (ZArith_dec.Z_lt_le_dec a 0).
      { revert H'; apply Z.max_case_strong; rewrite ?Zdiv.Zmod_0_l; intros; omega. }
      rewrite Z.max_r in * by assumption.
      let e := match goal with |- _ mod 2^Z.of_nat ?e = _ => e end in
      pose proof (Z.pos_pow_nat_pos 2 e).
      rewrite Z.mod_small_iff in * by (auto; omega).
      destruct H' as [H'|]; [ | lia ].
      left.
      split; [ omega | ].
      eapply Z.lt_le_trans; [ apply H' | ]; clear H'.
      cbv [wt base] in *.
      break_innermost_match.
      cbv [QArith_base.Qle QArith_base.inject_Z QArith_base.Qden QArith_base.Qnum] in *.
      cbn in *.
      autorewrite with zsimplify_const in *.
      rewrite Pos.mul_1_r in *.
      Z.peel_le.
      rewrite Z.pow_Zpow, Znat.Z2Nat.id by apply Z.log2_up_nonneg.
      cbn.
      rewrite Z.opp_le_mono; autorewrite with zsimplify_fast.
      apply Z.div_le_lower_bound; [ lia | ].
      rewrite Z.opp_le_mono; autorewrite with zsimplify_fast.
      rewrite <- Z.mul_opp_r, Z.mul_comm; autorewrite with zsimplify_fast.
      rewrite H; Z.peel_le.
      apply Z.log2_up_le_full. }
    { assumption. }
  Qed.

  Lemma encode_helper_from_bounded v
        (lgsz := Z.to_nat (Z.log2_up bitwidth))
        (H : ZRange.is_bounded_by None bounds_limb_widths v)
    : Tuple.map (fun x : Z => Z.max 0 x mod wt 1) v = v.
  Proof.
    pose proof curve_sc.(base_le_bitwidth) as H'.
    pose proof curve_sc.(wt_nonzero) as Hwtnz.
    pose proof curve_sc.(wt_nonneg) as Hwtnn.
    pose proof curve_sc.(wt_div_bound) as Hwt_good.
    cbv [bounds_limb_widths lgsz bounds' bounds_exponents'] in *.
    change (wt_gen curve.(base)) with wt in *.
    cbv [ZRange.is_bounded_by] in H.
    etransitivity; [ | apply Tuple.map_id ].
    rewrite <- (Tuple.map_id v) in H.
    rewrite <- !Tuple.fieldwise_eq_iff, !Tuple.fieldwise_map_iff.
    rewrite Tuple.map_map in H.
    rewrite Tuple.fieldwise_map_iff in H.
    cbv [ZRange.is_bounded_by'] in H; cbn in H.
    match goal with
    | [ |- ?B ] => cut (B /\ Tuple.fieldwise eq v v)
    end;
      [ intros P; apply P; auto; reflexivity | ].
    rewrite !Tuple.fieldwise_lift_and.
    eapply Tuple.fieldwise_Proper;
      [ cbv [Morphisms.pointwise_relation Basics.impl]
      | reflexivity..
      | ].
    { lazymatch goal with
      | [ |- forall a b, ?e a b -> @?f a b /\ a = b ]
        => unify e (fun a b => f b b /\ a = b); intros ?? [? ?]
      end.
      subst; auto. }
    cbv beta.
    rewrite <- !Tuple.fieldwise_lift_and; split; [ | reflexivity ].
    revert H.
    eapply (@Tuple.fieldwise_Proper_gen_dep _ _ _ _ (fun _ _ => True) eq Basics.impl _ (fun x => x));
      [ intros ?? _ ??? [H'' _]; subst
      | now rewrite Tuple.fieldwise_to_list_iff, ListUtil.Forall2_forall_iff
        by (rewrite ?Tuple.length_to_list; trivial; try constructor)
      | reflexivity ].
    rewrite Z.max_r by omega.
    rewrite Z.mod_small; [ reflexivity | ].
    split; [ omega | ].
    eapply Z.le_lt_trans; [ apply H'' | clear H'' ].
    match goal with
    | [ |- ?x - 1 < ?y ] => cut (x <= y); [ omega | ]
    end.
    pose proof (Hwtnz 1).
    pose proof (Hwtnn 1); cbn in *.
    cbv [Pos.to_nat] in *.
    cbn in *.
    rewrite Z.log2_le_pow2 by omega.
    Z.peel_le.
    auto.
  Qed.

  Require Import Coq.Compat.AdmitAxiom.

  Lemma Fencode_bounded v
    : ZRange.is_bounded_by None bounds_limb_widths (curve.(FencodeTuple) v).
  Proof.
    pose proof curve_sc.(sz_nonzero) as Hsz.
    pose proof curve_sc.(wt_nonzero) as Hwtnz.
    pose proof curve_sc.(wt_nonneg) as Hwtnn.
    pose proof curve_sc.(m_enc_minus_1_bounded_fieldwise) as Hm.
    pose proof curve_sc.(m_enc_minus_1_correct) as Hm'.
    cbv [bounds_limb_widths ZRange.is_bounded_by ZRange.is_bounded_by' bounds' bounds_exponents' m_enc m_enc' m_enc_minus_1 m_enc_minus_1' FencodeTuple] in *.
    rewrite !Tuple.map_map, <- (Tuple.map_id (Positional.Fencode _ _)), !Tuple.fieldwise_map_iff; cbn.
    change (wt_gen curve.(base)) with wt in *.
    lazymatch goal with
    | [ |- Tuple.fieldwise (fun x y => @?a x y <= @?b x y <= @?f x y - 1 /\ True) ?t1 ?t2 ]
      => cut (Tuple.fieldwise (fun x y => a x y <= b x y < f x y) t1 t2); cbv beta
    end.
    { apply Tuple.fieldwise_Proper;
        [ intros ???; split; trivial; omega | reflexivity.. ]. }
    revert Hsz Hwtnz Hwtnn Hm Hm' v.
    generalize wt sz m; intros wt sz m; revert wt sz m; clear.
    admit. (* TODO(jadep): FIXME *)
  Qed.

  Lemma encodeW_correct
    : forall v, curve.(decodeRaw) TW (Interp (curve.(encodeRaw) TW v) tt) = v.
  Proof.
    apply encode_correct_helper; intro; apply encodeW_correct_helper, encode_helper_from_bounded, Fencode_bounded.
  Qed.
End gen.
