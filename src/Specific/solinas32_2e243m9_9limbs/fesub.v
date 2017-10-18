Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e243m9_9limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
