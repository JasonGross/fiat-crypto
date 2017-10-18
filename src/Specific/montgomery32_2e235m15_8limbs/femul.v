Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e235m15_8limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
