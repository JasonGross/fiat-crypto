Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e216m2e108m1_4limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
