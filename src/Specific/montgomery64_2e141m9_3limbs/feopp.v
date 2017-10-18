Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e141m9_3limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
