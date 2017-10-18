Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e521m1_19limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
