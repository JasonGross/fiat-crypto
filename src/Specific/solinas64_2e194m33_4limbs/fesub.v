Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e194m33_4limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
