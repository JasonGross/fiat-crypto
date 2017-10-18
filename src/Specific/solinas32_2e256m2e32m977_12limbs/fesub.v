Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e256m2e32m977_12limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
