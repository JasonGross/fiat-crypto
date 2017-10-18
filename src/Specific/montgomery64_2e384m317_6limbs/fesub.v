Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e384m317_6limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
