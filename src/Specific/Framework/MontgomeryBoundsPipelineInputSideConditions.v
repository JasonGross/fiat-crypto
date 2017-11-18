Require Import Coq.ZArith.BinIntDef.
Require Import Coq.omega.Omega.
Require Import Coq.micromega.Lia.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Tuple.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.Z.Bounds.Interpretation.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Eta.
Require Import Crypto.Compilers.EtaInterp.
Require Import Crypto.Compilers.Linearize.
Require Import Crypto.Compilers.LinearizeInterp.
Require Import Crypto.Compilers.Tuple.
Require Import Crypto.Util.SideConditions.CorePackages.
Require Import Crypto.Util.SideConditions.ReductionPackages.
Require Import Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Montgomery.
Require Import Crypto.Specific.Framework.OutputType.
Require Import Crypto.Specific.Framework.BoundsPipelineInputSideConditions.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.ListUtil.
Import CurveParameters.Notations.

Local Set Implicit Arguments.
Local Coercion Z.to_nat : Z >-> nat.
Local Notation interp_flat_type := (interp_flat_type interp_base_type).

Section gen.
  Context (curve : CurveParameters.CurveParameters)
          (curve_sc : CurveParameterBaseSideConditions curve)
          (curve_scbm : CurveParameterMontgomeryBaseSideConditions curve)
          (curve_scm : montgomery_side_conditions curve_scbm).

  Local Notation wt := curve.(wt).
  Local Notation lgwt := curve.(lgwt).
  Local Notation m := curve.(m).
  Local Notation sz := curve.(sz).
  Local Notation r := curve.(r).
  Local Notation bitwidth := curve.(bitwidth).
  Local Notation allowable_bit_widths := curve.(allowable_bit_widths).
  Local Notation freeze_allowable_bit_widths := curve.(freeze_allowable_bit_widths).
  Local Notation bounds_tight := curve.(bounds_tight).
  Local Notation bounds_loose := curve.(bounds_loose).
  Local Notation bounds_limb_widths := curve.(bounds_limb_widths).
  Local Notation bounds_bitwidths := curve.(bounds_bitwidths).
  Local Notation bound1 := curve.(bound1).

  Local Notation TW := (TWord (Z.log2_up bitwidth)).
  Local Notation tZ := (Tbase TZ).
  Local Notation tW := (Tbase TW).
  Local Notation RT := (curve.(RT)).
  Local Notation rT := (curve.(rT)).
  Local Notation RTZ := (RT TZ).
  Local Notation rTZ := (rT TZ).
  Local Notation RTW := (RT TW).
  Local Notation rTW := (rT TW).
  Local Notation T' := curve.(T').

  Local Notation allowable_lgsz := (List.map Nat.log2 allowable_bit_widths).

  Local Notation pick_typeb := (@Interpretation.Bounds.bounds_to_base_type (Interpretation.Bounds.round_up_to_in_list allowable_lgsz)) (only parsing).
  Local Notation pick_type v := (SmartFlatTypeMap pick_typeb v).

  Local Notation is_limb_width a
    := (ZRange.is_bounded_by None bounds_limb_widths (flat_interp_tuple (T:=Tbase TZ) a))
         (only parsing).

  Local Notation η e := (ExprEta (Linearize (ExprEta e%expr))).

  Definition ropsZ : SynthesisOutputOps curve TZ
    := {|
        decodeZ v := curve_scbm.(montgomery_to_F) (MontgomeryAPI.eval (Z.pos r) v);
        encodeZ v := MontgomeryAPI.encode (Z.pos r) _ (curve_scbm.(montgomery_of_F) v);
        zero := η (val curve_scm.(zeroZ));
        one := η (val curve_scm.(oneZ));
        add := η (val curve_scm.(addZ));
        sub := η (val curve_scm.(subZ));
        opp := η (val curve_scm.(oppZ));
        carry := η (fun var => Abs (fun x => SmartVarf x));
        carry_mul := η (val curve_scm.(mulZ));
        carry_square := η (curve_scm.(val_squareZ));
        freeze := None;
        nonzero := Some (η (val curve_scm.(nonzeroZ)));
      |}.

  Definition P_extra : SynthesisOutputProps curve TZ
    := let eval := MontgomeryAPI.eval (Z.pos r) in
       let P_ A := is_limb_width A
                   -> UniformWeight.small (Z.pos r)
                                          (flat_interp_tuple (T:=Tbase TZ) A)
                      /\ eval (flat_interp_tuple (T:=Tbase TZ) A) < eval curve.(m_enc) in
       {|
         P_tight := P_;
         P_loose := P_;
         P_1 := fun _ => True;
         P_relax := fun _ pf => pf;
       |}.

  Lemma bounded_of_small v
    : UniformWeight.small (Z.pos r) v
      <-> ZRange.is_bounded_by None bounds_limb_widths v.
  Proof.
    pose proof curve_sc.(bitwidth_pos).
    rewrite curve_scm.(limb_width_is_bitwidth).
    cbv [UniformWeight.small ZRange.is_bounded_by r].
    cbv [bounds_bitwidths bounds' ZRange.is_bounded_by' ZRange.lower ZRange.upper].
    rewrite <- (Tuple.map_id v), Tuple.fieldwise_map_iff, Tuple.map_id, Tuple.fieldwise_to_list_iff, Z2Pos.id
      by (apply Z.pow_pos_nonneg; lia).
    assert (Hle : forall x, x < 2^bitwidth <-> x <= 2^bitwidth - 1) by (intros; lia).
    setoid_rewrite Hle.
    split.
    { rewrite Forall2_forall_iff' with (d:=0) by (rewrite !Tuple.length_to_list; reflexivity).
      intros H' i H''; split; trivial.
      eapply nth_default_preserves_properties; auto; rewrite <- Hle.
      split; try lia; apply Z.pow_pos_nonneg; lia. }
    { intros H' x.
      induction H'; simpl; try tauto.
      destruct_head'_and.
      intros [H''|H'']; subst; specialize_by_assumption; try lia. }
  Qed.


  Definition HP_extra : SynthesisOutputOpsValid' ropsZ P_extra.
  Proof.
    pose proof curve_scm.(tight_is_limb_width).
    pose proof curve_scm.(loose_is_limb_width).
    simple refine (let nonzeroZ_valid := _ in
                   {| nonzero_valid := nonzeroZ_valid |});
      [ | clearbody nonzeroZ_valid.. ];
      cbn [P_tight P_loose P_1 P_relax P_extra ropsZ zero one add sub opp carry carry_mul carry_square freeze nonzero] in *;
      pose proof curve_scm.(not_freeze);
      try (intros; exact I);
      try (intros; assumption);
      try congruence;
      pose proof curve_scbm.(r_big);
      pose proof (eval_nonzeroZ curve_sc curve_scm) as Hf;
      pose proof (fun v => @MontgomeryAPI.small_encode r ltac:(omega) sz _ (curve_scbm.(montgomery_of_F_bounded) v)) as Hs;
      setoid_rewrite bounded_of_small in Hs.
    rewrite curve_scm.(tight_is_limb_width); auto;
      repeat match goal with
             | _ => progress destruct_head'_sig
             | [ |- context[val ?e] ]
               => progress (destruct e; subst; cbn [val])
             | [ |- Compiler.compile_tupleZ _ = _ ]
               => cbv [OutputType.RT OutputType.rT encode Compiler.compile_tupleZ Compiler.compile_const Positional.Fencode F.to_Z]
             | _ => progress cbn [proj1_sig Interp interp interpf interpf_step smart_interp_flat_map option_map interpToZ]
             | _ => progress cbv [tuple_map zeroE_sig' oneE_sig' Compiler.compile_tupleZ Compiler.compile_const decodeZ option_map]
             | _ => progress intros
             | _ => progress cbn [domain codomain RTZ interp_flat_type]; cbv [rTZ]
             | _ => rewrite interpf_SmartPairf
             | _ => rewrite SmartVarfMap_compose
             | _ => rewrite Tuple.map_id
             | _ => rewrite Tuple.map_map
             | _ => rewrite flat_interp_tuple_untuple
             | _ => rewrite InterpProofs.interpf_SmartVarf
             | _ => rewrite SmartVarfMap_tuple; cbv [SmartVarfMap]
             | _ => cbn [interpToZ]; rewrite Tuple.map_id
             | _ => progress cbv [tuple_map vm_decide_package val_squareZ] in *
             | _ => reflexivity
             | _ => assumption
             | [ H : ?b = bounds_limb_widths, H' : context[?b] |- _ ]
               => rewrite H in H'
             | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
             | [ |- _ /\ _ ] => apply conj
             end.
    all:let app_tac _ :=
            lazymatch goal with
            | [ |- context[curve_scm.(addZ)] ]
              => apply (bounded_eval_addZ curve_sc curve_scm)
            | [ |- context[curve_scm.(oppZ)] ]
              => apply (bounded_eval_oppZ curve_sc curve_scm)
            | [ |- context[curve_scm.(subZ)] ]
              => apply (bounded_eval_subZ curve_sc curve_scm)
            | [ |- context[curve_scm.(mulZ)] ]
              => apply (bounded_eval_mulZ curve_sc curve_scm)
            end in
        repeat match goal with
               | [ |- _ < _ ] => app_tac ()
               | [ |- UniformWeight.small _ _ ] => app_tac ()
               | _ => assumption
               | _ => progress destruct_head'_and
               | _ => progress cbn [fst snd]
               | _ => rewrite (eval_nonzeroZ curve_sc curve_scm)
               end.
    Require Import AdmitAxiom.
    revert H2; clear; admit.
    revert H2; clear; admit.
    { cbv [eval evalF evalE preeval decodeZ montgomery_to_F evalZ Positional.Fdecode interpToZ MontgomeryAPI.eval].
      break_match; try reflexivity; exfalso.
      admit. }
    all:admit.
  Qed.

  Local Ltac interpose f :=
    etransitivity; [ | etransitivity; [ eapply f | ] ].

  Definition curve_scib : BoundsInputSideConditions ropsZ P_extra.
  Proof.
    pose proof curve_scm.(tight_is_limb_width).
    pose proof curve_scm.(loose_is_limb_width).
    constructor; intros; rewrite ?InterpCompose;
      cbv [carry opp add sub carry_mul]; cbn [ropsZ];
        repeat rewrite ?InterpExprEta_arrow, ?InterpLinearize;
        change (Interp (fun var => @?f var)) with (interp interp_op (f _));
        cbv [interp];
        try rewrite InterpProofs.interpf_SmartVarf;
        cbv [decode decodeToTuple interpToZ]; rewrite !Tuple.map_id;
          cbv [ropsZ decodeZ];
          cbn [P_tight P_extra] in *;
          repeat match goal with
                 | [ H : ?b = bounds_limb_widths, H' : context[?b] |- _ ]
                   => rewrite H in H'
                 | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
                 | _ => progress destruct_head'_and
                 end;
          lazymatch goal with
          | [ |- context[curve_scm.(addZ)] ]
            => interpose (fun x y => eval_addZ curve_sc curve_scm (x, y))
          | [ |- context[curve_scm.(oppZ)] ]
            => interpose (eval_oppZ curve_sc curve_scm)
          | [ |- context[curve_scm.(subZ)] ]
            => interpose (fun x y => eval_subZ curve_sc curve_scm (x, y))
          | [ |- context[curve_scm.(mulZ)] ]
            => interpose (fun x y => eval_mulZ curve_sc curve_scm (x, y))
          end;
          try reflexivity;
          try assumption.
  Qed.
End gen.
