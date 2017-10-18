Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.NISTP256.AMD128.Synthesis.

Time Definition nonzero := Eval lazy in invert_Some package.(opsW).(nonzero).
