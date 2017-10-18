Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e196m15_5limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
