Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e166m5_6limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
