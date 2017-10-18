Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e256m2e32m977_8limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
