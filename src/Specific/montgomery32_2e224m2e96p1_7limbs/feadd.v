Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e224m2e96p1_7limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
