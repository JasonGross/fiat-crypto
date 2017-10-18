Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e137m13_5limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
