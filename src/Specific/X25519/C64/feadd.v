Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.X25519.C64.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
