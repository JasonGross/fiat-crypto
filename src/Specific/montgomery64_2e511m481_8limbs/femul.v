Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e511m481_8limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
