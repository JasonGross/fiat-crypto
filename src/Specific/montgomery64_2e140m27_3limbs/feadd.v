Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e140m27_3limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
