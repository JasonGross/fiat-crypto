Require Import Crypto.SpecificGen.GF25519_64Reflective.Reified.LadderStep.
Require Export Crypto.Reflection.Syntax.
Require Export Bedrock.Word.
Require Export Crypto.Util.Notations.

Local Open Scope expr_scope.

Notation "'slet' x : T := A 'in' b" := (LetIn (tx:=T) A (fun x => b))
                                         (at level 200, b at level 200, format "'slet'  x  :  T  :=  A  'in' '//' b")
                                       : expr_scope.
Notation "T x = A ; b" := (LetIn (tx:=T) A (fun x => b))
                                         (at level 200, b at level 200, format "T  x  =  A ; '//' b")
                                       : expr_scope.
(*Notation uint32_t := (_ (TWord 5)).
Notation uint128_t := (_ (TWord 6)).
Notation uint128_t := (_ (TWord 7)).*)
Notation bool := (Tbase (TWord 0)).
Notation "'unsigned' 'short'" := (Tbase (TWord 1)).
Notation "'unsigned' 'short'" := (Tbase (TWord 2)).
Notation uint8_t := (Tbase (TWord 3)).
Notation uint16_t := (Tbase (TWord 4)).
Notation uint32_t := (Tbase (TWord 5)).
Notation uint64_t := (Tbase (TWord 6)).
Notation uint128_t := (Tbase (TWord 7)).
Notation "'(bool)' x" := (Op (Cast _ (TWord 0)) x) (at level 200, x at level 9).
Notation "'(unsigned short)' x" := (Op (Cast _ (TWord 1)) x) (at level 200, x at level 9).
Notation "'(unsigned short)' x" := (Op (Cast _ (TWord 2)) x) (at level 200, x at level 9).
Notation "'(uint8_t)' x" := (Op (Cast _ (TWord 3)) x) (at level 200, x at level 9).
Notation "'(uint16_t)' x" := (Op (Cast _ (TWord 4)) x) (at level 200, x at level 9).
Notation "'(uint32_t)' x" := (Op (Cast _ (TWord 5)) x) (at level 200, x at level 9).
Notation "'(uint64_t)' x" := (Op (Cast _ (TWord 6)) x) (at level 200, x at level 9).
Notation "'(uint128_t)' x" := (Op (Cast _ (TWord 7)) x) (at level 200, x at level 9).
Notation "'(bool)' x" := (Op (Cast _ (TWord 0)) (Var x)) (at level 200, x at level 9).
Notation "'(unsigned short)' x" := (Op (Cast _ (TWord 1)) (Var x)) (at level 200, x at level 9).
Notation "'(unsigned short)' x" := (Op (Cast _ (TWord 2)) (Var x)) (at level 200, x at level 9).
Notation "'(uint8_t)' x" := (Op (Cast _ (TWord 3)) (Var x)) (at level 200, x at level 9).
Notation "'(uint16_t)' x" := (Op (Cast _ (TWord 4)) (Var x)) (at level 200, x at level 9).
Notation "'(uint32_t)' x" := (Op (Cast _ (TWord 5)) (Var x)) (at level 200, x at level 9).
Notation "'(uint64_t)' x" := (Op (Cast _ (TWord 6)) (Var x)) (at level 200, x at level 9).
Notation "'(uint128_t)' x" := (Op (Cast _ (TWord 7)) (Var x)) (at level 200, x at level 9).
Notation "x + y" := (Op (Add _) (Pair x y)).
Notation "x + y" := (Op (Add _) (Pair (Var x) y)).
Notation "x + y" := (Op (Add _) (Pair x (Var y))).
Notation "x + y" := (Op (Add _) (Pair (Var x) (Var y))).
Notation "x - y" := (Op (Sub _) (Pair x y)).
Notation "x - y" := (Op (Sub _) (Pair (Var x) y)).
Notation "x - y" := (Op (Sub _) (Pair x (Var y))).
Notation "x - y" := (Op (Sub _) (Pair (Var x) (Var y))).
Notation "x * y" := (Op (Mul _) (Pair x y)).
Notation "x * y" := (Op (Mul _) (Pair (Var x) y)).
Notation "x * y" := (Op (Mul _) (Pair x (Var y))).
Notation "x * y" := (Op (Mul _) (Pair (Var x) (Var y))).
(* python:
<<
for opn, op in (('*', 'Mul'), ('+', 'Add'), ('&', 'Land')):
    for lgwordsz in (5, 6, 7):
        for side in ('l', 'r'):
            for v1 in (False, True):
                for v2 in (False, True):
                    lhs = ('x' if not v1 else '(Var x)')
                    lhs = (lhs if side != 'l' else '(Op (Cast _ (TWord %d)) %s)' % (lgwordsz, lhs))
                    rhs = ('y' if not v2 else '(Var y)')
                    rhs = (rhs if side != 'r' else '(Op (Cast _ (TWord %d)) %s)' % (lgwordsz, rhs))
                    print('Notation "x %s y" := (Op (%s (TWord %d)) (Pair %s %s)).' % (opn, op, lgwordsz, lhs, rhs))
>> *)
Notation "x * y" := (Op (Mul (TWord 5)) (Pair (Op (Cast _ (TWord 5)) x) y)).
Notation "x * y" := (Op (Mul (TWord 5)) (Pair (Op (Cast _ (TWord 5)) x) (Var y))).
Notation "x * y" := (Op (Mul (TWord 5)) (Pair (Op (Cast _ (TWord 5)) (Var x)) y)).
Notation "x * y" := (Op (Mul (TWord 5)) (Pair (Op (Cast _ (TWord 5)) (Var x)) (Var y))).
Notation "x * y" := (Op (Mul (TWord 5)) (Pair x (Op (Cast _ (TWord 5)) y))).
Notation "x * y" := (Op (Mul (TWord 5)) (Pair x (Op (Cast _ (TWord 5)) (Var y)))).
Notation "x * y" := (Op (Mul (TWord 5)) (Pair (Var x) (Op (Cast _ (TWord 5)) y))).
Notation "x * y" := (Op (Mul (TWord 5)) (Pair (Var x) (Op (Cast _ (TWord 5)) (Var y)))).
Notation "x * y" := (Op (Mul (TWord 6)) (Pair (Op (Cast _ (TWord 6)) x) y)).
Notation "x * y" := (Op (Mul (TWord 6)) (Pair (Op (Cast _ (TWord 6)) x) (Var y))).
Notation "x * y" := (Op (Mul (TWord 6)) (Pair (Op (Cast _ (TWord 6)) (Var x)) y)).
Notation "x * y" := (Op (Mul (TWord 6)) (Pair (Op (Cast _ (TWord 6)) (Var x)) (Var y))).
Notation "x * y" := (Op (Mul (TWord 6)) (Pair x (Op (Cast _ (TWord 6)) y))).
Notation "x * y" := (Op (Mul (TWord 6)) (Pair x (Op (Cast _ (TWord 6)) (Var y)))).
Notation "x * y" := (Op (Mul (TWord 6)) (Pair (Var x) (Op (Cast _ (TWord 6)) y))).
Notation "x * y" := (Op (Mul (TWord 6)) (Pair (Var x) (Op (Cast _ (TWord 6)) (Var y)))).
Notation "x * y" := (Op (Mul (TWord 7)) (Pair (Op (Cast _ (TWord 7)) x) y)).
Notation "x * y" := (Op (Mul (TWord 7)) (Pair (Op (Cast _ (TWord 7)) x) (Var y))).
Notation "x * y" := (Op (Mul (TWord 7)) (Pair (Op (Cast _ (TWord 7)) (Var x)) y)).
Notation "x * y" := (Op (Mul (TWord 7)) (Pair (Op (Cast _ (TWord 7)) (Var x)) (Var y))).
Notation "x * y" := (Op (Mul (TWord 7)) (Pair x (Op (Cast _ (TWord 7)) y))).
Notation "x * y" := (Op (Mul (TWord 7)) (Pair x (Op (Cast _ (TWord 7)) (Var y)))).
Notation "x * y" := (Op (Mul (TWord 7)) (Pair (Var x) (Op (Cast _ (TWord 7)) y))).
Notation "x * y" := (Op (Mul (TWord 7)) (Pair (Var x) (Op (Cast _ (TWord 7)) (Var y)))).
Notation "x + y" := (Op (Add (TWord 5)) (Pair (Op (Cast _ (TWord 5)) x) y)).
Notation "x + y" := (Op (Add (TWord 5)) (Pair (Op (Cast _ (TWord 5)) x) (Var y))).
Notation "x + y" := (Op (Add (TWord 5)) (Pair (Op (Cast _ (TWord 5)) (Var x)) y)).
Notation "x + y" := (Op (Add (TWord 5)) (Pair (Op (Cast _ (TWord 5)) (Var x)) (Var y))).
Notation "x + y" := (Op (Add (TWord 5)) (Pair x (Op (Cast _ (TWord 5)) y))).
Notation "x + y" := (Op (Add (TWord 5)) (Pair x (Op (Cast _ (TWord 5)) (Var y)))).
Notation "x + y" := (Op (Add (TWord 5)) (Pair (Var x) (Op (Cast _ (TWord 5)) y))).
Notation "x + y" := (Op (Add (TWord 5)) (Pair (Var x) (Op (Cast _ (TWord 5)) (Var y)))).
Notation "x + y" := (Op (Add (TWord 6)) (Pair (Op (Cast _ (TWord 6)) x) y)).
Notation "x + y" := (Op (Add (TWord 6)) (Pair (Op (Cast _ (TWord 6)) x) (Var y))).
Notation "x + y" := (Op (Add (TWord 6)) (Pair (Op (Cast _ (TWord 6)) (Var x)) y)).
Notation "x + y" := (Op (Add (TWord 6)) (Pair (Op (Cast _ (TWord 6)) (Var x)) (Var y))).
Notation "x + y" := (Op (Add (TWord 6)) (Pair x (Op (Cast _ (TWord 6)) y))).
Notation "x + y" := (Op (Add (TWord 6)) (Pair x (Op (Cast _ (TWord 6)) (Var y)))).
Notation "x + y" := (Op (Add (TWord 6)) (Pair (Var x) (Op (Cast _ (TWord 6)) y))).
Notation "x + y" := (Op (Add (TWord 6)) (Pair (Var x) (Op (Cast _ (TWord 6)) (Var y)))).
Notation "x + y" := (Op (Add (TWord 7)) (Pair (Op (Cast _ (TWord 7)) x) y)).
Notation "x + y" := (Op (Add (TWord 7)) (Pair (Op (Cast _ (TWord 7)) x) (Var y))).
Notation "x + y" := (Op (Add (TWord 7)) (Pair (Op (Cast _ (TWord 7)) (Var x)) y)).
Notation "x + y" := (Op (Add (TWord 7)) (Pair (Op (Cast _ (TWord 7)) (Var x)) (Var y))).
Notation "x + y" := (Op (Add (TWord 7)) (Pair x (Op (Cast _ (TWord 7)) y))).
Notation "x + y" := (Op (Add (TWord 7)) (Pair x (Op (Cast _ (TWord 7)) (Var y)))).
Notation "x + y" := (Op (Add (TWord 7)) (Pair (Var x) (Op (Cast _ (TWord 7)) y))).
Notation "x + y" := (Op (Add (TWord 7)) (Pair (Var x) (Op (Cast _ (TWord 7)) (Var y)))).
Notation "x >> y" := (Op (Shr _) (Pair x y)).
Notation "x >> y" := (Op (Shr _) (Pair (Var x) y)).
Notation "x >> y" := (Op (Shr _) (Pair x (Var y))).
Notation "x >> y" := (Op (Shr _) (Pair (Var x) (Var y))).
Notation "x >> y" := (Op (Shr _) (Pair x (Op (Cast _ _) y))).
Notation "x >> y" := (Op (Shr _) (Pair (Var x) (Op (Cast _ _) y))).
Notation "x >> y" := (Op (Shr _) (Pair x (Op (Cast _ _) (Var y)))).
Notation "x >> y" := (Op (Shr _) (Pair (Var x) (Op (Cast _ _) (Var y)))).
Notation "x & y" := (Op (Land _) (Pair x y)) (at level 40).
Notation "x & y" := (Op (Land _) (Pair (Var x) y)).
Notation "x & y" := (Op (Land _) (Pair x (Var y))).
Notation "x & y" := (Op (Land _) (Pair (Var x) (Var y))).
Notation "x & y" := (Op (Land (TWord 5)) (Pair (Op (Cast _ (TWord 5)) x) y)).
Notation "x & y" := (Op (Land (TWord 5)) (Pair (Op (Cast _ (TWord 5)) x) (Var y))).
Notation "x & y" := (Op (Land (TWord 5)) (Pair (Op (Cast _ (TWord 5)) (Var x)) y)).
Notation "x & y" := (Op (Land (TWord 5)) (Pair (Op (Cast _ (TWord 5)) (Var x)) (Var y))).
Notation "x & y" := (Op (Land (TWord 5)) (Pair x (Op (Cast _ (TWord 5)) y))).
Notation "x & y" := (Op (Land (TWord 5)) (Pair x (Op (Cast _ (TWord 5)) (Var y)))).
Notation "x & y" := (Op (Land (TWord 5)) (Pair (Var x) (Op (Cast _ (TWord 5)) y))).
Notation "x & y" := (Op (Land (TWord 5)) (Pair (Var x) (Op (Cast _ (TWord 5)) (Var y)))).
Notation "x & y" := (Op (Land (TWord 6)) (Pair (Op (Cast _ (TWord 6)) x) y)).
Notation "x & y" := (Op (Land (TWord 6)) (Pair (Op (Cast _ (TWord 6)) x) (Var y))).
Notation "x & y" := (Op (Land (TWord 6)) (Pair (Op (Cast _ (TWord 6)) (Var x)) y)).
Notation "x & y" := (Op (Land (TWord 6)) (Pair (Op (Cast _ (TWord 6)) (Var x)) (Var y))).
Notation "x & y" := (Op (Land (TWord 6)) (Pair x (Op (Cast _ (TWord 6)) y))).
Notation "x & y" := (Op (Land (TWord 6)) (Pair x (Op (Cast _ (TWord 6)) (Var y)))).
Notation "x & y" := (Op (Land (TWord 6)) (Pair (Var x) (Op (Cast _ (TWord 6)) y))).
Notation "x & y" := (Op (Land (TWord 6)) (Pair (Var x) (Op (Cast _ (TWord 6)) (Var y)))).
Notation "x & y" := (Op (Land (TWord 7)) (Pair (Op (Cast _ (TWord 7)) x) y)).
Notation "x & y" := (Op (Land (TWord 7)) (Pair (Op (Cast _ (TWord 7)) x) (Var y))).
Notation "x & y" := (Op (Land (TWord 7)) (Pair (Op (Cast _ (TWord 7)) (Var x)) y)).
Notation "x & y" := (Op (Land (TWord 7)) (Pair (Op (Cast _ (TWord 7)) (Var x)) (Var y))).
Notation "x & y" := (Op (Land (TWord 7)) (Pair x (Op (Cast _ (TWord 7)) y))).
Notation "x & y" := (Op (Land (TWord 7)) (Pair x (Op (Cast _ (TWord 7)) (Var y)))).
Notation "x & y" := (Op (Land (TWord 7)) (Pair (Var x) (Op (Cast _ (TWord 7)) y))).
Notation "x & y" := (Op (Land (TWord 7)) (Pair (Var x) (Op (Cast _ (TWord 7)) (Var y)))).
Notation Return x := (Var x).
Notation "'0b10'" := (Const WO~1~0). (* 2 *)
Notation "'0b00010011'" := (Const WO~0~0~0~1~0~0~1~1). (* 19 *)
Notation "'0b00011001'" := (Const WO~0~0~0~1~1~0~0~1). (* 25 *)
Notation "'0b00011010'" := (Const WO~0~0~0~1~1~0~1~0). (* 26 *)
Notation "'0b00000011111111111111111111111111'" := (Const WO~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0b00000001111111111111111111111111'" := (Const WO~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0b00000011111111111111111111111110'" := (Const WO~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0b00000111111111111111111111011010'" := (Const WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1~0).
Notation "'0b00110011'" := (Const WO~0~0~1~1~0~0~1~1).
Notation "'0b0000000000000111111111111111111111111111111111111111111111111111'"
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0b0000000000001111111111111111111111111111111111111111111111111110'"
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0b0000000000001111111111111111111111111111111111111111111111011010'"
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1~0).
Notation C_like := (Common.Expr _).
Print rladderstepW.
