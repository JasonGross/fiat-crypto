Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e444m17_8limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
