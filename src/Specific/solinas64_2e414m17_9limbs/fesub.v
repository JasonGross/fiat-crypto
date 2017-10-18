Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e414m17_9limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
