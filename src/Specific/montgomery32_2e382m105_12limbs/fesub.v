Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e382m105_12limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
