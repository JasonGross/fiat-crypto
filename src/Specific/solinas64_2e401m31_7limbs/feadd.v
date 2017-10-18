Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e401m31_7limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
