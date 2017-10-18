Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e382m105_6limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
