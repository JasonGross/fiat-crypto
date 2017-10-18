Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e137m13_5limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
