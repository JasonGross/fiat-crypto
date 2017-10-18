Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e224m2e96p1_5limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
