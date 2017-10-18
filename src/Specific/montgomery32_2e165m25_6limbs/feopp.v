Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e165m25_6limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
