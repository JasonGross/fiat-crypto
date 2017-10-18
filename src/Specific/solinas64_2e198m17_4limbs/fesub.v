Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e198m17_4limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
