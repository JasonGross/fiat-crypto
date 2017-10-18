Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e226m5_9limbs.Synthesis.

Time Definition freeze := Eval lazy in invert_Some package.(opsW).(freeze).
