Require Import Crypto.SpecificGen.GF2519_32Reflective.Reified.Add.
Require Export Crypto.Reflection.Syntax.

Local Open Scope expr_scope.

Notation "'slet' x : T := A 'in' b" := (LetIn (tx:=T) A (fun x => b))
                                         (at level 200, b at level 200, format "'slet'  x  :  T  :=  A  'in' '//' b")
                                       : expr_scope.
Notation "T x = A ; b" := (LetIn (tx:=T) A (fun x => b))
                                         (at level 200, b at level 200, format "T  x  =  A ; '//' b")
                                       : expr_scope.
Notation uint32_t := (Tbase (TWord 5)).
Notation uint64_t := (Tbase (TWord 6)).
Notation uint128_t := (Tbase (TWord 7)).
Notation "x + y" := (Op (Add _) (Pair (Var x) (Var y))).
Notation Return x := (Var x).
Print raddW.
