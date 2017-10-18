Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e222m117_5limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
