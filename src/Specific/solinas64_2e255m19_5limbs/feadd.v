Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e255m19_5limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
