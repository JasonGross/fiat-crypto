Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e174m3_7limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
