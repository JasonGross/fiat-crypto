Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e510m290x2e496m1_16limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
