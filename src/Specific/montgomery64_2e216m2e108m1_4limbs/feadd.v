Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e216m2e108m1_4limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
