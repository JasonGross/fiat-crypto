Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e256m2e32m977_7limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
