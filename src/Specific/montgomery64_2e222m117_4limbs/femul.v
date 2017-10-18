Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e222m117_4limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
