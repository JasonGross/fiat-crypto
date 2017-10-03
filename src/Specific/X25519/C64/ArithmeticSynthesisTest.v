Require Import Crypto.Specific.ArithmeticSynthesisFramework.
Require Import Crypto.Specific.X25519.C64.CurveParameters.

Module S := Synthesize Curve.

Set Ltac Profiling.
Definition synthesized' : ArithmeticSynthesisTestPackage.
Proof. Time S.synthesize (). Time Defined.
Show Ltac Profile.

Time Definition synthesized :=
  Eval cbv zeta delta [synthesized'] in synthesized'.

Global Existing Instance synthesized.
