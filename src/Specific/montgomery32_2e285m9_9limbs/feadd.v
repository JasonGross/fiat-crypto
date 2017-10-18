Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e285m9_9limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
