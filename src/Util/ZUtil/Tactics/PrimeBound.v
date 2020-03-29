Require Import Coq.omega.Omega Coq.ZArith.Znumtheory.
Require Export Crypto.Util.FixCoqMistakes.
Require Export Crypto.Util.GlobalSettings.

Module Z.
  Ltac prime_bound := match goal with
  | [ H : prime ?p |- _ ] => pose proof (prime_ge_2 p H); try omega
  end.
End Z.
