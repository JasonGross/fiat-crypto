Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e190m11_3limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
