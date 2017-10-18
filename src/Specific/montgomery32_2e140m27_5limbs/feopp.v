Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e140m27_5limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
