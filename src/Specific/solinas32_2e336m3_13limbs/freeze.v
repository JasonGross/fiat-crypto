Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e336m3_13limbs.Synthesis.

Time Definition freeze := Eval lazy in invert_Some package.(opsW).(freeze).
