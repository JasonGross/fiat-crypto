Require Export Crypto.Util.FixCoqMistakes.
Require Export Crypto.Util.GlobalSettings.

Ltac clear_duplicates_step :=
  match goal with
  | [ H : ?T, H' : ?T |- _ ] => clear H'
  | [ H := ?T, H' := ?T |- _ ] => clear H'
  end.
Ltac clear_duplicates := repeat clear_duplicates_step.
