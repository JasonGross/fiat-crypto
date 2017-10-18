Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e254m127x2e240m1_4limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
