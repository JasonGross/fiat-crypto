Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e221m3_7limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
