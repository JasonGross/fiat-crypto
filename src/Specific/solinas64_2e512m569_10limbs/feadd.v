Require Import Crypto.Specific.Framework.Synthesis.
Require Import Crypto.Specific.solinas64_2e512m569_10limbs.Synthesis.

Time Definition add := Eval lazy in package.(opsW).(add).
