Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e480m2e240m1_10limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
