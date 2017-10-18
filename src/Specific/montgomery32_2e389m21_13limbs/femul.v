Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e389m21_13limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
