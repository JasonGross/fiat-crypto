Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e189m25_8limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
