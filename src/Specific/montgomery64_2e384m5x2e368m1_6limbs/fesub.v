Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e384m5x2e368m1_6limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
