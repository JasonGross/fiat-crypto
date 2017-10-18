Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e158m15_3limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
