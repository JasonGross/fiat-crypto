Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e127m1_4limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
