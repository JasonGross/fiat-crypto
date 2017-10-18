Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e383m31_6limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
