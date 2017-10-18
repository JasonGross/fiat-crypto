Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e511m481_11limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
