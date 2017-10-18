Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e212m29_7limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
