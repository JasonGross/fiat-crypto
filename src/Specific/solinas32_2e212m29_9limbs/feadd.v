Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e212m29_9limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
