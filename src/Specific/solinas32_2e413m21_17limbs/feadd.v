Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e413m21_17limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
