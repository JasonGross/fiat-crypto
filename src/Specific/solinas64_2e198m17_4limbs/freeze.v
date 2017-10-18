Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e198m17_4limbs.Synthesis.

Time Definition freeze := Eval lazy in invert_Some package.(opsW).(freeze).
