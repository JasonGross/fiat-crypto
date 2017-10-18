Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e141m9_5limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
