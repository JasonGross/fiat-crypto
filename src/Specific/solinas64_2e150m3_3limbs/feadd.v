Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e150m3_3limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
