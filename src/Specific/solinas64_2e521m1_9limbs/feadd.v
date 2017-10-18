Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e521m1_9limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
