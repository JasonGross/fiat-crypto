Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e448m2e224m1_7limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
