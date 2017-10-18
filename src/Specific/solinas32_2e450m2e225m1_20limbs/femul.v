Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e450m2e225m1_20limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
