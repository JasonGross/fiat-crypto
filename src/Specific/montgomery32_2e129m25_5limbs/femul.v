Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e129m25_5limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
