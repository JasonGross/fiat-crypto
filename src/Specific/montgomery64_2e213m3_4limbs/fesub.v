Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e213m3_4limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
