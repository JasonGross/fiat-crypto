Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e166m5_7limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
