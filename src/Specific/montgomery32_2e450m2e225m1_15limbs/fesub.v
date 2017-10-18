Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e450m2e225m1_15limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
