Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e189m25_5limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
