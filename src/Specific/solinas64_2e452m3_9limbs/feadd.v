Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e452m3_9limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
