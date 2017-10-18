Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e266m3_5limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
