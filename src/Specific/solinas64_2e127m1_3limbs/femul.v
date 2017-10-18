Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e127m1_3limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
