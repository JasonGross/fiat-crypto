Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e452m3_17limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
