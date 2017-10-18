Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e448m2e224m1_14limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
