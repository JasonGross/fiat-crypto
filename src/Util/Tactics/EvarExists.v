Require Export Crypto.Util.FixCoqMistakes.
Require Export Crypto.Util.GlobalSettings.

(** Like [eexists], but stuffs the new evar in a context variable *)
Ltac evar_exists :=
  let T := fresh in
  let e := fresh in
  evar (T : Type); evar (e : T); subst T; exists e.
