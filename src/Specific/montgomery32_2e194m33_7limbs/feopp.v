Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e194m33_7limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
