Require Export Crypto.Util.FixCoqMistakes.
Require Export Crypto.Util.GlobalSettings.

Ltac subst_evars :=
  repeat match goal with
         | [ e := ?E |- _ ] => is_evar E; subst e
         end.
