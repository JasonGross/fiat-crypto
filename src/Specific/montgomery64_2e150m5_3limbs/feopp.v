Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e150m5_3limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
