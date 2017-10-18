Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e379m19_12limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
