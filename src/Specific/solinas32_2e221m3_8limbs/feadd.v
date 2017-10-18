Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e221m3_8limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
