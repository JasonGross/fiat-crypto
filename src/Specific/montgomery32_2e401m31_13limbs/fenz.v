Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e401m31_13limbs.Synthesis.

Time Definition nonzero := Eval lazy in invert_Some package.(opsW).(nonzero).
