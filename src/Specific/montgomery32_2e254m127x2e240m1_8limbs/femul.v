Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e254m127x2e240m1_8limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
