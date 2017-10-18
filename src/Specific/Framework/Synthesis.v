Require Export Crypto.Specific.Framework.OutputType.
Require Export Crypto.Util.Option.
Require Import Crypto.Specific.Framework.Pipeline.
Require Import Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Specific.Framework.BoundsPipeline.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Solinas.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Montgomery.
Require Import Crypto.Util.SideConditions.Autosolve.
Require Import Crypto.Compilers.Z.Reify.
Require Import Crypto.Util.Tactics.Not.

Module Internal.
  Ltac autosolve_gen autosolve_tac else_tac :=
    lazymatch goal with
    | [ |- SynthesisOutput ?e ]
      => not has_evar e; unshelve eapply @Pipeline;
         autosolve_tac else_tac
    | [ |- CurveParameterBaseSideConditions ?e ]
      => not has_evar e; unshelve econstructor;
         autosolve_tac else_tac
    | [ |- PipelineSideConditions ?e _ ]
      => not has_evar e; unshelve econstructor;
         autosolve_tac else_tac
    | [ |- Solinas.solinas_side_conditions ?e ]
      => not has_evar e; unshelve econstructor;
         autosolve_tac else_tac
    | [ |- Montgomery.montgomery_side_conditions ?e ]
      => not has_evar e; unshelve econstructor;
         autosolve_tac else_tac
    | [ |- Montgomery.CurveParameterMontgomeryBaseSideConditions ?e ]
      => not has_evar e; unshelve econstructor;
         autosolve_tac else_tac
    | [ |- BoundsPipeline.BoundsSideConditions ?e ]
      => not has_evar e; unshelve econstructor;
         autosolve_tac else_tac
    | _ => else_tac ()
    end.
End Internal.

Ltac autosolve_gen autosolve_tac else_tac :=
  Autosolve.autosolve_gen autosolve_tac ltac:(fun _ =>
  Internal.autosolve_gen autosolve_tac ltac:(fun _ =>
  BoundsPipeline.autosolve ltac:(fun _ =>
  Z.Reify.autosolve ltac:(fun _ =>
  else_tac ()
                                             )))).

Ltac autosolve else_tac := autosolve_gen autosolve else_tac.

Ltac else_tac _ :=
  idtac "Failed to autosolve goal:";
  lazymatch goal with |- ?G => idtac G end.

Notation fill_defaults curve
  := (CurveParameters.CurveParameters.fill_CurveParameters curve)
       (only parsing).

Ltac synthesize _ :=
  autosolve else_tac.

Ltac synthesize_step _ := autosolve_gen ltac:(fun _ => idtac) else_tac.
