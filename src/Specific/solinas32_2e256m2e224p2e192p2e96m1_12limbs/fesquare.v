Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e256m2e224p2e192p2e96m1_12limbs.Synthesis.

Time Definition square := Eval lazy in package.(opsW).(carry_square).
