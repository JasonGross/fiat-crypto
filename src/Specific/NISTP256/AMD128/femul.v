Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.NISTP256.AMD128.Synthesis.

Time Definition mul := Eval lazy in package.(opsW).(carry_mul).
