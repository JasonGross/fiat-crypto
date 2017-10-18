Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e194m33_8limbs.Synthesis.

Time Definition square := Eval lazy in package.(opsW).(carry_square).
