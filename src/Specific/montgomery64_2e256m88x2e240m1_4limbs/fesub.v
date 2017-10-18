Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e256m88x2e240m1_4limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
