Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e127m1_6limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
