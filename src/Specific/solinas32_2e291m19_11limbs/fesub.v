Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e291m19_11limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
