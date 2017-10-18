Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.X25519.C32.Synthesis.

Time Definition freeze := Eval lazy in invert_Some package.(opsW).(freeze).
