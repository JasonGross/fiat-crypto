Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e369m25_15limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
