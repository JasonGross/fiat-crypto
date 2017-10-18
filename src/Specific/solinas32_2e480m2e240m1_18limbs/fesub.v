Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e480m2e240m1_18limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
