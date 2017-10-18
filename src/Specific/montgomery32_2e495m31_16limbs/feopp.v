Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e495m31_16limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
