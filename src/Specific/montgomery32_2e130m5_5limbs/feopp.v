Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e130m5_5limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
