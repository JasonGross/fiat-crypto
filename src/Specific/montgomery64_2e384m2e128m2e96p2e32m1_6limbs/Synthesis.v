Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e384m2e128m2e96p2e32m1_6limbs.CurveParameters.

Definition curve := fill_defaults curve.

Definition package : SynthesisOutput curve.
Proof.
  Set Ltac Profiling.
  Time synthesize ().
  Show Ltac Profile.
Time Defined.

(* Time Print Assumptions package. *)
