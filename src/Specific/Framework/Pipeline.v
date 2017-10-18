Require Import Coq.ZArith.BinIntDef.
Require Import Coq.omega.Omega.
Require Import Coq.micromega.Lia.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Compilers.Z.Bounds.Pipeline.Definition.
Require Import Crypto.Compilers.Z.Bounds.Pipeline.ReflectiveTactics.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Tuple.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Tuple.
Require Import Crypto.Util.SideConditions.CorePackages.
Require Import Crypto.Util.SideConditions.ReductionPackages.
Require Import Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Solinas.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Montgomery.
Require Export Crypto.Specific.Framework.OutputType.
Require Import Crypto.Specific.Framework.MontgomeryBoundsPipelineInputSideConditions.
Require Import Crypto.Specific.Framework.SolinasBoundsPipelineInputSideConditions.
Require Import Crypto.Specific.Framework.BoundsPipelineInputSideConditions.
Require Import Crypto.Specific.Framework.BoundsPipeline.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.ZUtil.Tactics.PeelLe.
Require Import Crypto.Util.ZUtil.Tactics.ReplaceNegWithPos.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.
Import CurveParameters.Notations.

Local Set Implicit Arguments.
Local Coercion Z.to_nat : Z >-> nat.
Local Notation interp_flat_type := (interp_flat_type interp_base_type).

Section gen.
  Context (curve : CurveParameters.CurveParameters)
          (curve_sc' : vm_decide_package (CurveParameterBaseSideConditions_bool curve = true)).

  Definition curve_sc
    := CurveParameterBaseSideConditions_bool_correct curve curve_sc'.

  Record SolinasPipelineSC :=
    {
      ssc :> solinas_side_conditions curve_sc;
      sropsZ := SolinasBoundsPipelineInputSideConditions.ropsZ ssc;
      sP_extra := SolinasBoundsPipelineInputSideConditions.P_extra curve;
      sHP_extra := SolinasBoundsPipelineInputSideConditions.HP_extra ssc;
      scurve_scib := SolinasBoundsPipelineInputSideConditions.curve_scib ssc;
      sbounds :> BoundsSideConditions sropsZ;
    }.

  Record MontgomeryPipelineSC :=
    {
      mscb :> CurveParameterMontgomeryBaseSideConditions curve;
      msc :> montgomery_side_conditions mscb;
      mropsZ := MontgomeryBoundsPipelineInputSideConditions.ropsZ msc;
      mP_extra := MontgomeryBoundsPipelineInputSideConditions.P_extra curve;
      mHP_extra := MontgomeryBoundsPipelineInputSideConditions.HP_extra curve_sc msc;
      mcurve_scib := MontgomeryBoundsPipelineInputSideConditions.curve_scib curve_sc msc;
      mbounds :> BoundsSideConditions mropsZ;
    }.

  Definition PipelineSideConditions
    := if curve.(montgomery)
       then MontgomeryPipelineSC
       else SolinasPipelineSC.

  Context (sc : PipelineSideConditions).

  Definition Pipeline : SynthesisOutput curve.
  Proof.
    hnf in sc.
    pose curve_sc.
    (destruct curve.(montgomery) eqn:?);
      destruct sc;
      unshelve eapply @BoundsPipeline; assumption.
  Defined.
End gen.

(** Overwrite the [RBPipelineSideConditions_unfold] stub with the
    things we should actually unfold, now that we have access to
    them. *)
Ltac RBPipelineSideConditions_unfold ::=
  cbv [val
         Option.invert_Some Build_evard_package
         SolinasBoundsPipelineInputSideConditions.ropsZ
         (* OutputType *)
         OutputType.zero
         OutputType.one
         OutputType.add
         OutputType.sub
         OutputType.carry_mul
         OutputType.carry_square
         OutputType.opp
         OutputType.carry
         OutputType.freeze
         OutputType.nonzero
         OutputType.carry_add
         OutputType.carry_sub
         OutputType.carry_opp
         (* Solinas *)
         Solinas.not_montgomery
         Solinas.vm_compiled_preadd
         Solinas.vm_compiled_presub
         Solinas.vm_compiled_premul
         Solinas.vm_compiled_preopp
         Solinas.vm_compiled_prereduce
         Solinas.vm_compiled_prereduce_sz_sz
         Solinas.vm_compiled_prereduce_sz_1p5
         Solinas.vm_compiled_prechained_carries_reduce
         Solinas.vm_compiled_prekaratsuba_mul
         Solinas.vm_compiled_pregoldilocks_mul
         Solinas.vm_compiled_prefreeze
         Solinas.mul_code_correct
         Solinas.square_code_correct
         Solinas.evalZ
         Solinas.evalZ2
         Solinas.evalZ1p5
         Solinas.evalE
         Solinas.evalE2
         Solinas.evalE1p5
         Solinas.eval
         Solinas.eval2
         Solinas.eval1p5
         Solinas.mul_code_casted
         Solinas.square_code_casted
         Solinas.mul_codeZ
         Solinas.square_codeZ
         Solinas.zeroZ
         Solinas.oneZ
         Solinas.addZ
         Solinas.subZ
         Solinas.oppZ
         Solinas.carryZ
         Solinas.reduceZ
         Solinas.reduceZ_sz_sz
         Solinas.reduceZ_sz_1p5
         Solinas.premulZ
         Solinas.val_presquareZ
         Solinas.prekaratsuba_mulZ
         Solinas.pregoldilocks_mulZ
         Solinas.val_prekaratsuba_squareZ
         Solinas.val_pregoldilocks_squareZ
         Solinas.freezeZ
         Solinas.carry_mulZ
         Solinas.carry_squareZ
         Solinas.carry_addZ
         Solinas.carry_subZ
         Solinas.carry_oppZ].
