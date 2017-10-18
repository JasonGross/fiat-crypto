Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e141m9_3limbs.Synthesis.

Time Definition freeze := Eval lazy in invert_Some package.(opsW).(freeze).
