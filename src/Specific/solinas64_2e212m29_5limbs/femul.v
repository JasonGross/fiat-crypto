Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e212m29_5limbs.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
