Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e141m9_4limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
