Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e383m187_7limbs.Synthesis.

Time Definition sub := Eval lazy in package.(opsW).(sub).
