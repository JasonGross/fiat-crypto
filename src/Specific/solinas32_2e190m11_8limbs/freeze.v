Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e190m11_8limbs.Synthesis.

Time Definition freeze := Eval lazy in invert_Some package.(opsW).(freeze).
