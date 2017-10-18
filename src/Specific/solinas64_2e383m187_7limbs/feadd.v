Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e383m187_7limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
