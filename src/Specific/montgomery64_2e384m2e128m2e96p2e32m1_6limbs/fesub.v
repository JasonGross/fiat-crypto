Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e384m2e128m2e96p2e32m1_6limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
