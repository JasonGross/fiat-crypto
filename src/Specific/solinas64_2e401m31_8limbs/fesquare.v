Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e401m31_8limbs.Synthesis.

Time Definition square := Eval lazy in package.(opsW).(carry_square).
