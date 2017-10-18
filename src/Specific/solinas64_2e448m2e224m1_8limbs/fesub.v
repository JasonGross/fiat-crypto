Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e448m2e224m1_8limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
