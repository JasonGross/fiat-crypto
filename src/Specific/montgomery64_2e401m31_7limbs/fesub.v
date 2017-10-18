Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e401m31_7limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
