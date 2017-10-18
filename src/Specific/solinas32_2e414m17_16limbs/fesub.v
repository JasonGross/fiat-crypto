Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e414m17_16limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
