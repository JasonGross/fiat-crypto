Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e251m9_10limbs.Synthesis.

Time Definition square := Eval lazy in package.(opsW).(carry_square).
