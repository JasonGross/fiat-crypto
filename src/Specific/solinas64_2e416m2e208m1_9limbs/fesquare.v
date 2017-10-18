Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e416m2e208m1_9limbs.Synthesis.

Time Definition square := Eval lazy in package.(opsW).(carry_square).
