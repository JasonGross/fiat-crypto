Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e512m491x2e496m1_8limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
