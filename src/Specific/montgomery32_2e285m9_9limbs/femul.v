Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e285m9_9limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
