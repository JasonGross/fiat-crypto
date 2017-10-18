Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e165m25_7limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
