Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e489m21_9limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
