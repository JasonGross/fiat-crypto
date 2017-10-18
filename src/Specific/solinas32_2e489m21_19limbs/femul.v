Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e489m21_19limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
