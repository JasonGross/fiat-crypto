Require Export Crypto.Util.FixCoqMistakes.
Require Export Crypto.Util.GlobalSettings.

(** Checks if a hypothesis has a body *)

Ltac has_body x := let test := eval unfold x in x in idtac.
