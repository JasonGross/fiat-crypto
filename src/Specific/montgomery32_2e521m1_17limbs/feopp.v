Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e521m1_17limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
