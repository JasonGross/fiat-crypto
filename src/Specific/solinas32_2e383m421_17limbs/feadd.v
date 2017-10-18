Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e383m421_17limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
