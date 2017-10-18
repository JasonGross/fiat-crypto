Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e444m17_18limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
