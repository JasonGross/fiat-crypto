Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e384m317_8limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
