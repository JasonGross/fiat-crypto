Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e191m19_8limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
