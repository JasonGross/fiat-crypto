Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e448m2e224m1_18limbs.Synthesis.

Time Definition square := Eval lazy in package.(opsW).(carry_square).
