Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e256m189_6limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
