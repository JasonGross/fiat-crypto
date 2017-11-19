Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e450m2e225m1_8limbs.CurveParameters.

Definition curve := fill_defaults curve.

Definition package : SynthesisOutput curve.
Proof.
  Set Ltac Profiling.
  Time synthesize ().
  Show Ltac Profile.
Time Defined.

(* Time Print Assumptions package. *)
