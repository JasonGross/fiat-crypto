Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e256m189_4limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
