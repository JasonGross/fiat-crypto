Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e152m17_7limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
