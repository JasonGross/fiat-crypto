Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e383m31_15limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
