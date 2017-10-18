Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.X2448.Karatsuba.C64.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
