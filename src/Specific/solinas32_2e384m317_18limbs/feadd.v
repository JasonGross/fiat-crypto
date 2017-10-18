Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e384m317_18limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
