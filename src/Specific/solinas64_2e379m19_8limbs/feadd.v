Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e379m19_8limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
