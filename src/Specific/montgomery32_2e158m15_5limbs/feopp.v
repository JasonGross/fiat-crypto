Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e158m15_5limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
