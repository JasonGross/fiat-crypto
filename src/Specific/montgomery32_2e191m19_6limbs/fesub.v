Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e191m19_6limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
