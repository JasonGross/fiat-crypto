Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e413m21_13limbs.Synthesis.

Time Definition nonzero := Eval lazy in invert_Some package.(opsW).(nonzero).
