Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e369m25_12limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
