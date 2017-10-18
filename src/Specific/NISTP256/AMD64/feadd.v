Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.NISTP256.AMD64.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
