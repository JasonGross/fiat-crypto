Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e266m3_5limbs.Synthesis.

Time Definition square := Eval lazy in package.(opsW).(carry_square).
