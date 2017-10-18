Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e511m187_11limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
