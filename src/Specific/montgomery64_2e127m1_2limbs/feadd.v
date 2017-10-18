Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e127m1_2limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
