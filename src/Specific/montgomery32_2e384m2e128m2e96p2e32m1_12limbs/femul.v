Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e384m2e128m2e96p2e32m1_12limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
