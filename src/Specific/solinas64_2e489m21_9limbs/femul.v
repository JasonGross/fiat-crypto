Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e489m21_9limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
