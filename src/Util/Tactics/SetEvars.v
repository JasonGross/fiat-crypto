Require Export Crypto.Util.FixCoqMistakes.
Require Export Crypto.Util.GlobalSettings.

Ltac set_evars :=
  repeat match goal with
         | [ |- context[?E] ] => is_evar E; let e := fresh "e" in set (e := E)
         end.
