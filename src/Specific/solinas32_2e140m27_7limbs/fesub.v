Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e140m27_7limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
