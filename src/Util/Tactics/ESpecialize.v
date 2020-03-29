Require Export Crypto.Util.FixCoqMistakes.
Require Export Crypto.Util.GlobalSettings.

(** Like [specialize] but allows holes that get filled with evars. *)
Tactic Notation "especialize" open_constr(H) := specialize H.
