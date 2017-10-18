Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e140m27_6limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
