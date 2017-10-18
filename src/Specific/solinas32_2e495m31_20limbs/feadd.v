Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e495m31_20limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
