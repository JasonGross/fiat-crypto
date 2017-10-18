Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e266m3_9limbs.Synthesis.

Time Definition opp := Eval lazy in package.(opsW).(opp).
