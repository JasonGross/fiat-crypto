Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e266m3_6limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
