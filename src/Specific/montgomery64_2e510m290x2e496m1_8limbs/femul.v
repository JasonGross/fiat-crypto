Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e510m290x2e496m1_8limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
