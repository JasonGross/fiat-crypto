Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e369m25_8limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
