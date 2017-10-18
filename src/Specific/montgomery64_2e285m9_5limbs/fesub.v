Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e285m9_5limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
