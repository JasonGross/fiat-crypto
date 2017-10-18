Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e480m2e240m1_8limbs.Synthesis.

Time Definition nonzero := Eval lazy in invert_Some package.(opsW).(nonzero).
