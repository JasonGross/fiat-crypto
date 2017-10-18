Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e256m2e224p2e192p2e96m1_6limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
