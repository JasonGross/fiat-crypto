Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e322m2e161m1_12limbs.Synthesis.

Time Definition square := Eval lazy in package.(opsW).(carry_square).
