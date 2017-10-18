Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e226m5_8limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
