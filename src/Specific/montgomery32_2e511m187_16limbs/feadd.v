Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.montgomery32_2e511m187_16limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
