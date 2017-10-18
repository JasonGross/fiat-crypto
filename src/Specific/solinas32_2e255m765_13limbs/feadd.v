Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e255m765_13limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
