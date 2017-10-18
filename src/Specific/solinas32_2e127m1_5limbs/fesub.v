Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e127m1_5limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
