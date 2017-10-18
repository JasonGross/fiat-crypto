Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas32_2e383m187_17limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
