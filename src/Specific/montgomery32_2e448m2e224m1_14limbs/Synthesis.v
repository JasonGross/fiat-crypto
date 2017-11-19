Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e448m2e224m1_14limbs.CurveParameters.

Definition curve := fill_defaults curve.

Definition package : SynthesisOutput curve.
Proof.
  Set Ltac Profiling.
  Time synthesize ().
  Show Ltac Profile.
Time Defined.

(* Time Print Assumptions package. *)
