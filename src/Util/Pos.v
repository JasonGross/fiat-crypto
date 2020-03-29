Require Import Coq.PArith.BinPosDef.
Require Export Crypto.Util.FixCoqMistakes.
Require Export Crypto.Util.GlobalSettings.

Local Open Scope positive_scope.
(** Append two sequences *)

Fixpoint app (p q:positive) : positive :=
  match q with
  | q~0 => (app p q)~0
  | q~1 => (app p q)~1
  | 1 => p~1
  end.
