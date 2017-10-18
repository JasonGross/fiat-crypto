Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e251m9_4limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
