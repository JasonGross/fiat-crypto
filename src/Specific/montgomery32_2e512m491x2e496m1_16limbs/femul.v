Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e512m491x2e496m1_16limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
