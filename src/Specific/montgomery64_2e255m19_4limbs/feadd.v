Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e255m19_4limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
