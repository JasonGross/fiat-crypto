Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e512m569_8limbs.Synthesis.

Time Definition nonzero := Eval lazy in invert_Some package.(opsW).(nonzero).
