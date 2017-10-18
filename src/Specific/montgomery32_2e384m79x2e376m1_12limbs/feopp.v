Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e384m79x2e376m1_12limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
