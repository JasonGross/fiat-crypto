Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e216m2e108m1_7limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
