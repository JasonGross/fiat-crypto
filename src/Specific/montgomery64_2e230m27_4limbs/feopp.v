Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e230m27_4limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
