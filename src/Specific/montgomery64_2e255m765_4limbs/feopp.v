Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e255m765_4limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
