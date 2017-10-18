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
Require Import Crypto.Compilers.Tuple.
Require Import Crypto.Util.SideConditions.CorePackages.
Require Import Crypto.Util.SideConditions.ReductionPackages.
Require Import Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Solinas.
Require Import Crypto.Specific.Framework.OutputType.
Require Import Crypto.Specific.Framework.OutputTypeLemmas.
Require Import Crypto.Specific.Framework.BoundsPipelineInputSideConditions.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.ListUtil.
Import CurveParameters.Notations.

Local Set Implicit Arguments.
Local Coercion Z.to_nat : Z >-> nat.
Local Notation interp_flat_type := (interp_flat_type interp_base_type).

Section gen.
  Context (curve : CurveParameters.CurveParameters)
          (curve_sc : CurveParameterBaseSideConditions curve)
          (curve_scs : solinas_side_conditions curve_sc).

  Local Notation wt := curve.(wt).
  Local Notation lgwt := curve.(lgwt).
  Local Notation m := curve.(m).
  Local Notation sz := curve.(sz).
  Local Notation bitwidth := curve.(bitwidth).
  Local Notation allowable_bit_widths := curve.(allowable_bit_widths).
  Local Notation freeze_allowable_bit_widths := curve.(freeze_allowable_bit_widths).
  Local Notation bounds_tight := curve.(bounds_tight).
  Local Notation bounds_loose := curve.(bounds_loose).
  Local Notation bounds_limb_widths := curve.(bounds_limb_widths).
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

  Definition ropsZ : SynthesisOutputOps curve TZ
    := {|
        encodeZ := curve.(FencodeTuple);
        decodeZ := curve.(FdecodeTuple);
        zero := val curve_scs.(zeroZ);
        one := val curve_scs.(oneZ);
        add := val curve_scs.(addZ);
        sub := val curve_scs.(subZ);
        opp := val curve_scs.(oppZ);
        carry := val curve_scs.(carryZ);
        carry_mul := curve_scs.(carry_mulZ);
        carry_square := curve_scs.(carry_squareZ);
        freeze := val curve_scs.(freezeZ);
        nonzero := None;
      |}.

  Definition P_extra : SynthesisOutputProps curve TZ
    := {|
        P_tight := fun _ => True;
        P_loose := fun _ => True;
        P_1 := fun _ => True;
        P_relax := fun _ pf => pf;
      |}.

  Definition HP_extra : SynthesisOutputOpsValid' ropsZ P_extra.
  Proof.
    simple refine (let freezeZ_valid := _ in
                   {| freeze_valid := freezeZ_valid |});
      [ | clearbody freezeZ_valid.. ];
      cbn [P_tight P_loose P_1 P_relax P_extra ropsZ zero one add sub opp carry carry_mul carry_square freeze nonzero encode decode encodeZ decodeZ constant_sig'] in *;
      pose proof curve_scs.(not_montgomery);
      try (intros; exact I);
      try (intros; assumption);
      try congruence;
      pose proof curve_scs.(eval_freezeZ) as Hf;
      repeat match goal with
             | _ => progress destruct_head'_sig
             | [ |- context[val ?e] ]
               => progress (destruct e; subst; cbn [val])
             | [ |- Compiler.compile_tupleZ _ = _ ]
               => cbv [OutputType.RT OutputType.rT encode Compiler.compile_tupleZ Compiler.compile_const Positional.Fencode F.to_Z]
             | _ => progress cbn [proj1_sig Interp interp interpf interpf_step encodeTuple]
             | _ => progress cbv [tuple_map zeroE_sig' oneE_sig' Compiler.compile_tupleZ Compiler.compile_const decodeZ option_map constant_sig' encode]
             | _ => progress intros
             | _ => rewrite interpf_SmartPairf
             | _ => rewrite SmartVarfMap_compose
             | _ => rewrite Tuple.map_id
             | _ => rewrite Tuple.map_map
             | _ => rewrite flat_interp_tuple_untuple
             | _ => cbn [interpToZ]; rewrite Tuple.map_id
             | _ => cbv [decodeToTuple interpToZ]; rewrite Tuple.map_id
             | _ => setoid_rewrite SmartVarfMap_tuple; cbv [SmartVarfMap]
             | _ => apply curve_scs.(eval_carryZ)
             | _ => apply curve_scs.(eval_carry_mulZ)
             | _ => etransitivity; [ apply curve_scs.(eval_carry_squareZ) | symmetry ]
             | _ => reflexivity
             | _ => solve [ auto using curve_sc.(relax_limb_width_bounds), curve_sc.(Fencode_bounded), curve_sc.(FdecodeTuple_FencodeTuple) ]
             end;
      try lazymatch goal with
          | [ |- context[freezeZ] ]
            => edestruct freezeZ, vm_compiled_prefreeze; subst;
                 cbn [CorePackages.val] in *;
                 break_innermost_match_step; trivial;
                   break_innermost_match_hyps_step; try tauto; try discriminate
          end.
    { repeat first [ progress cbn [option_map interpToZ] in *
                   | rewrite Tuple.map_id
                   | progress cbv [eval evalZ evalE] in * ].
      apply Hf, curve_sc.(eval_bounded_tight); assumption. }
  Qed.

  Definition curve_scib : BoundsInputSideConditions ropsZ P_extra.
  Proof.
    constructor; intros;
      rewrite ?InterpCompose;
      cbv [decode decodeToTuple interpToZ]; rewrite !Tuple.map_id;
        try (setoid_rewrite curve_scs.(eval_carryZ); cbn).
    { setoid_rewrite curve_scs.(eval_oppZ). reflexivity. }
    { setoid_rewrite curve_scs.(eval_addZ); reflexivity. }
    { setoid_rewrite curve_scs.(eval_subZ); reflexivity. }
    { setoid_rewrite curve_scs.(eval_carry_mulZ); reflexivity. }
  Qed.
End gen.
