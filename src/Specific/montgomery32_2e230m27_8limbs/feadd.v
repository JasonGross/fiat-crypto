Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e230m27_8limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
