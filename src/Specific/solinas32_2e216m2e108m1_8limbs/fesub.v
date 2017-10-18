Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e216m2e108m1_8limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
