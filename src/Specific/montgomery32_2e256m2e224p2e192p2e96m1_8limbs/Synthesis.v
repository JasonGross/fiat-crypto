Require Import Crypto.Specific.Framework.Pipeline.
Require Import Crypto.Specific.montgomery32_2e256m2e224p2e192p2e96m1_8limbs.CurveParameters.

Definition curve := CurveParameters.CurveParameters.fill_CurveParameters curve.

  Require Import Crypto.Util.Tactics.Not.
  Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
  Require Import Crypto.Util.SideConditions.CorePackages.
  Require Import Crypto.Util.SideConditions.Autosolve.
  Notation vm_ev := (ReductionPackages.vm_compute_evar_package_gen _).
  Notation cast_ev := (ReductionPackages.cast_evar_package _ _).
  Notation option_ev := (ReductionPackages.option_evar_rel_package _ _ _ _).
  Notation vm_dec := (ReductionPackages.vm_decide_package _).
  Notation ring_pkg := (RingPackage.eq_by_Zring_prod_package _).
  Import Compilers.Syntax.

  Definition package : SynthesisOutput curve.
Proof.
  Set Ltac Profiling.
  Import Head.
  Ltac myfail := idtac "fail"; lazymatch goal with |- ?G => let h := head G in idtac h; idtac G end; fail.
  repeat lazymatch goal with
         | [ |- SynthesisOutput ?e ]
           => not has_evar e; unshelve eapply @Pipeline
         | [ |- CurveParameterBaseSideConditions ?e ]
           => not has_evar e; unshelve econstructor
         end.
  Time autosolve ltac:(fun _ => myfail).
  repeat lazymatch goal with
         | [ |- PipelineSideConditions ?e _ ]
           => not has_evar e; unshelve econstructor
         | [ |- Solinas.solinas_side_conditions ?e ]
           => not has_evar e; unshelve econstructor
         | [ |- Montgomery.montgomery_side_conditions ?e ]
           => not has_evar e; unshelve econstructor
         | [ |- Montgomery.CurveParameterMontgomeryBaseSideConditions ?e ]
           => not has_evar e; unshelve econstructor
         end.
  Time autosolve ltac:(fun _ => myfail).
  Time autosolve ltac:(fun _ => myfail).
  Time autosolve ltac:(fun _ => myfail).
  Time autosolve ltac:(fun _ => myfail).
  Time autosolve ltac:(fun _ => myfail).
  Time autosolve ltac:(fun _ => myfail).
  Time autosolve ltac:(fun _ => myfail).
  Time autosolve ltac:(fun _ => myfail).
  repeat lazymatch goal with
         | [ |- PipelineSideConditions ?e _ ]
           => not has_evar e; unshelve econstructor
         | [ |- Solinas.solinas_side_conditions ?e ]
           => not has_evar e; unshelve econstructor
         | [ |- Montgomery.montgomery_side_conditions ?e ]
           => not has_evar e; unshelve econstructor
         | [ |- Montgomery.CurveParameterMontgomeryBaseSideConditions ?e ]
           => not has_evar e; unshelve econstructor
         end.
  Time autosolve ltac:(fun _ => myfail).
  Time autosolve ltac:(fun _ => myfail).
  Time autosolve ltac:(fun _ => myfail).
  Time autosolve ltac:(fun _ => myfail).
  Time autosolve ltac:(fun _ => myfail).
  { Time autosolve ltac:(fun _ => myfail). }
  { Time autosolve ltac:(fun _ => myfail). }
  { Time autosolve ltac:(fun _ => myfail). }
  { Time autosolve ltac:(fun _ => myfail). }
  { Time autosolve ltac:(fun _ => myfail). }
  { Time autosolve ltac:(fun _ => myfail). }
  { Time autosolve ltac:(fun _ => myfail). }
  { Time autosolve ltac:(fun _ => myfail). }
  { Time autosolve ltac:(fun _ => myfail). }
  { Time autosolve ltac:(fun _ => myfail). }
  { Time autosolve ltac:(fun _ => myfail). }
  { Time
      repeat lazymatch goal with
             | [ |- SynthesisOutput ?e ]
               => not has_evar e; unshelve eapply @Pipeline
             | [ |- CurveParameterBaseSideConditions ?e ]
               => not has_evar e; unshelve econstructor
             | [ |- PipelineSideConditions ?e _ ]
               => not has_evar e; unshelve econstructor
             | [ |- Solinas.solinas_side_conditions ?e ]
               => not has_evar e; unshelve econstructor
             | [ |- Montgomery.montgomery_side_conditions ?e ]
               => not has_evar e; unshelve econstructor
             | [ |- Montgomery.CurveParameterMontgomeryBaseSideConditions ?e ]
               => not has_evar e; unshelve econstructor
             | [ |- BoundsPipeline.BoundsSideConditions ?e ]
               => not has_evar e; unshelve econstructor
             end.
    { idtac "here".
      { Time autosolve ltac:(fun _ => myfail). } }
    { Time autosolve ltac:(fun _ => myfail). }
    { Time autosolve ltac:(fun _ => BoundsPipeline.autosolve ltac:(fun _ => myfail)). }
    { Time autosolve ltac:(fun _ => BoundsPipeline.autosolve ltac:(fun _ => myfail)). }
    { Time autosolve ltac:(fun _ => BoundsPipeline.autosolve ltac:(fun _ => myfail)). }
    { Time autosolve ltac:(fun _ => BoundsPipeline.autosolve ltac:(fun _ => myfail)). }
    { Time autosolve ltac:(fun _ => BoundsPipeline.autosolve ltac:(fun _ => myfail)). }
    { Time autosolve ltac:(fun _ => BoundsPipeline.autosolve ltac:(fun _ => myfail)). }
    { Time autosolve ltac:(fun _ => BoundsPipeline.autosolve ltac:(fun _ => myfail)). }
    { Time autosolve ltac:(fun _ => BoundsPipeline.autosolve ltac:(fun _ => myfail)). } }
  Show Ltac Profile.
  Time Defined.
Time Print Assumptions package.


Definition zero := Eval lazy in zero (opsW package).
Definition one := Eval lazy in one (opsW package).
Definition add := Eval lazy in add (opsW package).
Definition sub := Eval lazy in sub (opsW package).
Definition opp := Eval lazy in opp (opsW package).
Definition carry_mul := Eval lazy in carry_mul (opsW package).
Definition carry_square := Eval lazy in carry_square (opsW package).
Definition nonzero := Eval lazy in nonzero (opsW package).
Definition freeze := Eval lazy in freeze (opsW package).

Require Import Framework.IntegrationTestDisplayCommon.

Print zero.
Print one.
Print add.
Print sub.
Print opp.
Print carry_mul.
Print carry_square.
Print nonzero.
Print freeze.

(*
Require Import CNotations.
Print SynthesisOutput.
Check opsW package.
Print SynthesisOutputOps.
Goal True.
  pose (sub (opsW package)) as e.
  Time lazy in e.
  Time Print Assumptions package.
  simple refine (let v := carry (opsZ (_ : SynthesisOutput curve)) in
                 _).
  clear e.
  unshelve eapply @Pipeline.
  autosolve ltac:(fun _ => fail).
  unshelve econstructor.
  unshelve econstructor.
  Focus 11.
  cbv [carry opsZ Pipeline] in v.
  cbv [CurveParameters.CurveParameters.montgomery curve ] in v.
  cbv [curve_sc] in v.
  cbv [MontgomeryBoundsPipelineInputSideConditions.ropsZ] in v.
  cbv [rT] in v.
  Timeout 2 lazy in v.
  cbv [CurveParameters.CurveParameters.sz] in v.
  Print BoundsPipeline.BoundsPipeline.
  cbv [BoundsPipeline.BoundsPipeline] in v.
compute in v.
  hnf in v.
  Locate
  Eval hnf in @Pipeline curve _ _. {| mropsZ := _ |}.
  Time vm_compute in e.
  idtac.
  Unset Silent.
  Time Show.
  Time idtac.
  pose (sub (opsW package)) as e.
  Time cbv [sub opsW package] in e.
  idtac.
  Unset Silent.
  Time Show.
  Time idtac.
  Notation hidden := (sub _).

Time Compute sub (opsW package).
(*Module P <: PrePackage.
  Definition package : Tag.Context.
  Proof. make_Synthesis_package curve extra_prove_mul_eq extra_prove_square_eq. Defined.
End P.

Module Export S := PackageSynthesis P.
*)
*)
