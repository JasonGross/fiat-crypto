Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e251m9_8limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
