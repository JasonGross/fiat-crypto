Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e322m2e161m1_7limbs.Synthesis.

Time Definition square := Eval lazy in package.(opsW).(carry_square).
