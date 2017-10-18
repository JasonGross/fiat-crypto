Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e413m21_16limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
