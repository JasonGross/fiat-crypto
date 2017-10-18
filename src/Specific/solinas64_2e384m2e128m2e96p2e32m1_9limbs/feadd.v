Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e384m2e128m2e96p2e32m1_9limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
