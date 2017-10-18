Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e338m15_11limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
