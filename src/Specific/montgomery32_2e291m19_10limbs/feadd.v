Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e291m19_10limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
