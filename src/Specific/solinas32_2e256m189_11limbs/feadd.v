Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e256m189_11limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
