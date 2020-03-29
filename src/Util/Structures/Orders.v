Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.Orders.
Require Export Crypto.Util.FixCoqMistakes.
Require Export Crypto.Util.GlobalSettings.

Module Type UsualEqLt := UsualEq <+ HasLt.
Module Type UsualEqLe := UsualEq <+ HasLe.
Module Type UsualEqLtLe := UsualEq <+ HasLt <+ HasLe.
