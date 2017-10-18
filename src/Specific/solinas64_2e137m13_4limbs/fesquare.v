Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e137m13_4limbs.Synthesis.

Time Definition square := Eval lazy in package.(opsW).(carry_square).
