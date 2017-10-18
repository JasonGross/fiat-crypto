Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e226m5_10limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
