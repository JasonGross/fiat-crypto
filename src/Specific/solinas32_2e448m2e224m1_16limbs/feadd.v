Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e448m2e224m1_16limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
