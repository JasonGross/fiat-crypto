Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e414m17_13limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
