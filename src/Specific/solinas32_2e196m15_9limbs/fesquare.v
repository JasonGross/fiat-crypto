Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e196m15_9limbs.Synthesis.

Time Definition square := Eval lazy in package.(opsW).(carry_square).
