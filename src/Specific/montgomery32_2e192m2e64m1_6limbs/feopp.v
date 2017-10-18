Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e192m2e64m1_6limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
