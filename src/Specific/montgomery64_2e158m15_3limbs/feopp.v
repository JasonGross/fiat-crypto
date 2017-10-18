Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e158m15_3limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
