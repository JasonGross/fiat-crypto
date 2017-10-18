Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e468m17_18limbs.Synthesis.

Time Definition square := Eval lazy in package.(opsW).(carry_square).
