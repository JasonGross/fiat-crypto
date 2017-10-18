Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e489m21_10limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
