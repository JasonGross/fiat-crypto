Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e444m17_14limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
