Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e205m45x2e198m1_7limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
