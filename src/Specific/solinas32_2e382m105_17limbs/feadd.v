Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e382m105_17limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
