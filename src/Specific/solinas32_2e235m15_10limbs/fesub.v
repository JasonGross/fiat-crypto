Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e235m15_10limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
