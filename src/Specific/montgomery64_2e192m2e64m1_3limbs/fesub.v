Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery64_2e192m2e64m1_3limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
