Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e255m19_8limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
