Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e140m27_4limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
