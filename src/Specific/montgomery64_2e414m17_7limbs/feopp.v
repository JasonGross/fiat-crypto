Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e414m17_7limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
