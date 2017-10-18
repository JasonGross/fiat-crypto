Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e521m1_10limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
