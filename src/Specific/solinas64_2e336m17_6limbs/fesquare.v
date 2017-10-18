Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e336m17_6limbs.Synthesis.

Time Definition square := Eval lazy in package.(opsW).(carry_square).
