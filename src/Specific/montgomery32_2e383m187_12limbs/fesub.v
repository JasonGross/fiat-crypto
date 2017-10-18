Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e383m187_12limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
