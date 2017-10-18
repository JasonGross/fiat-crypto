Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e224m2e96p1_6limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
