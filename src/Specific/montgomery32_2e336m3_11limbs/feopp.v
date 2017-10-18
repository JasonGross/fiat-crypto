Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e336m3_11limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
