Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e216m2e108m1_8limbs.CurveParameters.

Definition curve := fill_defaults curve.

Definition package : SynthesisOutput curve.
Proof.
  Set Ltac Profiling.
  Time synthesize ().
  Show Ltac Profile.
Time Defined.

(* Time Print Assumptions package. *)
