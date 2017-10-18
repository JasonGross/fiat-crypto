Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e338m15_14limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
