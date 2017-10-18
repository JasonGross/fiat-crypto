Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e221m3_5limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
