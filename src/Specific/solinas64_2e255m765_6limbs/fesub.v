Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e255m765_6limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
