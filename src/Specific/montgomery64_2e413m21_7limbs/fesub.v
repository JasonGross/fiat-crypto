Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e413m21_7limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
