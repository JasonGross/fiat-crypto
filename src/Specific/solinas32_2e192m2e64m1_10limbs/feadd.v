Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e192m2e64m1_10limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
