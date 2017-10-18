Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e336m3_7limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
