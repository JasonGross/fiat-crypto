Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e243m9_6limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
