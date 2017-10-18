Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e129m25_3limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
