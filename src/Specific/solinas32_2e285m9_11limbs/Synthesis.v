Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e285m9_11limbs.CurveParameters.

Definition curve := fill_defaults curve.

Definition package : SynthesisOutput curve.
Proof.
  Set Ltac Profiling.
  Time synthesize ().
  Show Ltac Profile.
Time Defined.

(* Time Print Assumptions package. *)
