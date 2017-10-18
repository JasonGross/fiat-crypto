Require Import Crypto.Specific.Framework.Pipeline.
Require Import Crypto.Specific.X25519.C64.CurveParameters.

Definition curve := CurveParameters.CurveParameters.fill_CurveParameters curve.

  Lemma rew_impl (a b : bool) : (if a then b else true) = implb a b.
  Proof. destruct a, b; reflexivity. Qed.
Definition package : SynthesisOutput curve.
Proof.
  Require Import Crypto.Util.Tactics.Not.
  Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
  Require Import Crypto.Util.SideConditions.CorePackages.
  Require Import Crypto.Util.SideConditions.Autosolve.
  Set Ltac Profiling.
  repeat lazymatch goal with
         | [ |- SynthesisOutput ?e ]
           => not has_evar e; unshelve eapply @Pipeline
         | [ |- CurveParameterBaseSideConditions ?e ]
           => not has_evar e; unshelve econstructor
         end.
  Time autosolve ltac:(fun _ => fail).
  repeat lazymatch goal with
         | [ |- PipelineSideConditions ?e _ ]
           => not has_evar e; unshelve econstructor
         | [ |- Solinas.solinas_side_conditions ?e ]
           => not has_evar e; unshelve econstructor
         end.
  Notation vm_ev := (ReductionPackages.vm_compute_evar_package_gen _).
  Notation cast_ev := (ReductionPackages.cast_evar_package _ _).
  Notation option_ev := (ReductionPackages.option_evar_rel_package _ _ _ _).
  Notation vm_dec := (ReductionPackages.vm_decide_package _).
  Notation ring_pkg := (RingPackage.eq_by_Zring_prod_package _).
  Import Compilers.Syntax.
  48-51:simpl @CurveParameters.CurveParameters.sz;
    cbv [Syntax.tuple Syntax.tuple' option_map val].
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  Time autosolve ltac:(fun _ => fail).
  { Require Import Crypto.Compilers.Reify.
    Require Import Crypto.Compilers.Z.Reify.
    Require Import Crypto.Util.SideConditions.Autosolve.
    Time autosolve ltac:(fun _ => fail). }
  { Time autosolve ltac:(fun _ => fail). }
  { Time autosolve ltac:(fun _ => fail). }
  { Time autosolve ltac:(fun _ => fail). }
  { Time autosolve ltac:(fun _ => fail). }
  { Time autosolve ltac:(fun _ => fail). }
  { Time autosolve ltac:(fun _ => fail). }
  { Time autosolve ltac:(fun _ => fail). }
  { Time autosolve ltac:(fun _ => fail). }
  { Time autosolve ltac:(fun _ => fail). }
  { Time autosolve ltac:(fun _ => fail). }
  { Time autosolve ltac:(fun _ => fail). }
  { Time autosolve ltac:(fun _ => fail). }
  { Time autosolve ltac:(fun _ => fail). }
  { Time autosolve ltac:(fun _ => fail). }
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
             | [ |- BoundsPipeline.BoundsSideConditions ?e ]
               => not has_evar e; unshelve econstructor
             end.
    { Time autosolve ltac:(fun _ => fail). }
    { Time autosolve ltac:(fun _ => fail). }
    { Time autosolve ltac:(fun _ => BoundsPipeline.autosolve ltac:(fun _ => fail)). }
    { Time autosolve ltac:(fun _ => BoundsPipeline.autosolve ltac:(fun _ => fail)). }
    { Time autosolve ltac:(fun _ => BoundsPipeline.autosolve ltac:(fun _ => fail)). }
    { Time autosolve ltac:(fun _ => BoundsPipeline.autosolve ltac:(fun _ => fail)). }
    { Time autosolve ltac:(fun _ => BoundsPipeline.autosolve ltac:(fun _ => fail)). }
    { Time autosolve ltac:(fun _ => BoundsPipeline.autosolve ltac:(fun _ => fail)). }
    { Time autosolve ltac:(fun _ => BoundsPipeline.autosolve ltac:(fun _ => fail)). }
    { vm_compute; reflexivity. } }
Time Defined.
