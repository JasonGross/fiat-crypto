Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e383m421_8limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
