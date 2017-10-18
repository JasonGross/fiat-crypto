Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e382m105_16limbs.Synthesis.

Time Definition square := Eval lazy in package.(opsW).(carry_square).
