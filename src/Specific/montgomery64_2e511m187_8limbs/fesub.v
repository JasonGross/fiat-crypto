Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e511m187_8limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
