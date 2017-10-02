Require Import Crypto.Specific.ArithmeticSynthesisFramework.
Require Import Crypto.Specific.X25519.C32.CurveParameters.

Module S := Synthesize Curve.

Definition synthesized' : ArithmeticSynthesisTestPackage.
Proof. Time S.synthesize (). Time Defined.

Time Definition synthesized :=
  Eval cbv zeta delta [synthesized'] in synthesized'.

Global Existing Instance synthesized.
