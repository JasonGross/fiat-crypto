Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e511m481_23limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
