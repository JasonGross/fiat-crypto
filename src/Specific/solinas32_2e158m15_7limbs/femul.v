Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e158m15_7limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
