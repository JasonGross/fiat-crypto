Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e322m2e161m1_6limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
