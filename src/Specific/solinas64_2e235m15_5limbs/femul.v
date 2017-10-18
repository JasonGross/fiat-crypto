Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e235m15_5limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
