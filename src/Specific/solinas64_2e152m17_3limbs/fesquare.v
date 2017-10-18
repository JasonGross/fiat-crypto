Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e152m17_3limbs.Synthesis.

Time Definition square := Eval lazy in package.(opsW).(carry_square).
