Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e285m9_11limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
