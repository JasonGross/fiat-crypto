Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e256m2e32m977_13limbs.Synthesis.

Time Definition square := Eval lazy in package.(opsW).(carry_square).
