Require Export Crypto.Util.FixCoqMistakes.
Require Export Crypto.Util.GlobalSettings.
Class with_default (T : Type) (default : T) := defaulted : T.
Global Instance by_default {T} {d} : with_default T d := d.
