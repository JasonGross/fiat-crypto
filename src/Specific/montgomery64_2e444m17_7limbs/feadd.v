Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e444m17_7limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
