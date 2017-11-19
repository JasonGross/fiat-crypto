Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e256m2e224p2e192p2e96m1_8limbs.CurveParameters.

Definition curve := fill_defaults curve.

Definition package : SynthesisOutput curve.
Proof.
  Set Ltac Profiling.
  Time synthesize ().
  Show Ltac Profile.
Time Defined.

(* Time Print Assumptions package. *)
