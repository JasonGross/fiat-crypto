Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e198m17_7limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
