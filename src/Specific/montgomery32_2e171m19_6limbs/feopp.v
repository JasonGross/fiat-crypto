Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e171m19_6limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
