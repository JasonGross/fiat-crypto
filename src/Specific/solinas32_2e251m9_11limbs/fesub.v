Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e251m9_11limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
