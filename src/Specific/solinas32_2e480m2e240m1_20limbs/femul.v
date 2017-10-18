Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e480m2e240m1_20limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
