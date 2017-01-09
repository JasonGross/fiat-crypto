Require Export Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Z.Syntax.
Require Export Bedrock.Word.
Require Export Crypto.Util.Notations.

Reserved Notation "T x = A ; b" (at level 200, b at level 200, format "T  x  =  A ; '//' b").
Reserved Notation "'(bool)' x" (at level 200, x at level 9).
Reserved Notation "'(unsigned short)' x" (at level 200, x at level 9).
Reserved Notation "'(uint8_t)' x" (at level 200, x at level 9).
Reserved Notation "'(uint16_t)' x" (at level 200, x at level 9).
Reserved Notation "'(uint32_t)' x" (at level 200, x at level 9).
Reserved Notation "'(uint64_t)' x" (at level 200, x at level 9).
Reserved Notation "'(uint128_t)' x" (at level 200, x at level 9).
Reserved Notation "x & y" (at level 40).

Global Open Scope expr_scope.

Notation "T x = A ; b" := (LetIn (tx:=T) A (fun x => b)) : expr_scope.
(*Notation uint32_t := (_ (TWord 5)).
Notation uint64_t := (_ (TWord 6)).
Notation uint128_t := (_ (TWord 7)).*)
Notation bool := (Tbase (TWord 0)).
Notation "'unsigned' 'short'" := (Tbase (TWord 1)).
Notation "'unsigned' 'short'" := (Tbase (TWord 2)).
Notation uint8_t := (Tbase (TWord 3)).
Notation uint16_t := (Tbase (TWord 4)).
Notation uint32_t := (Tbase (TWord 5)).
Notation uint64_t := (Tbase (TWord 6)).
Notation uint128_t := (Tbase (TWord 7)).
Notation "'(bool)' x" := (Op (Cast _ (TWord 0)) x).
Notation "'(unsigned short)' x" := (Op (Cast _ (TWord 1)) x).
Notation "'(unsigned short)' x" := (Op (Cast _ (TWord 2)) x).
Notation "'(uint8_t)' x" := (Op (Cast _ (TWord 3)) x).
Notation "'(uint16_t)' x" := (Op (Cast _ (TWord 4)) x).
Notation "'(uint32_t)' x" := (Op (Cast _ (TWord 5)) x).
Notation "'(uint64_t)' x" := (Op (Cast _ (TWord 6)) x).
Notation "'(uint128_t)' x" := (Op (Cast _ (TWord 7)) x).
Notation "'(bool)' x" := (Op (Cast _ (TWord 0)) (Var x)).
Notation "'(unsigned short)' x" := (Op (Cast _ (TWord 1)) (Var x)).
Notation "'(unsigned short)' x" := (Op (Cast _ (TWord 2)) (Var x)).
Notation "'(uint8_t)' x" := (Op (Cast _ (TWord 3)) (Var x)).
Notation "'(uint16_t)' x" := (Op (Cast _ (TWord 4)) (Var x)).
Notation "'(uint32_t)' x" := (Op (Cast _ (TWord 5)) (Var x)).
Notation "'(uint64_t)' x" := (Op (Cast _ (TWord 6)) (Var x)).
Notation "'(uint128_t)' x" := (Op (Cast _ (TWord 7)) (Var x)).
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
Notation "x & y" := (Op (Land _) (Pair x y)).
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
Notation C_like := (Expr base_type interp_base_type op _).
(* python:
<<
print('\n'.join('''Notation "'%s'" (* %d (%s) *)\n  := (Const %s).''' % (b, d, h, i) for d, h, b, i in sorted([(eval(bv), hex(eval(bv)), bv, i) for (bv, i) in (('0b' + i[2:].replace('~', ''), i) for i in r"""WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1~0
WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0
WO~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
WO~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0
WO~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1~0
WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~0
WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0
WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
WO~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0
WO~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
WO~0~0~0~1~0~0~1~1
WO~0~0~0~1~1~0~0~1
WO~0~0~0~1~1~0~1~0
WO~0~0~0~1~1~0~1~1
WO~0~0~0~1~1~1~0~0
WO~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~0
WO~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0
WO~0~0~1~1~0~0~1~1
WO~1~0
WO~1~0~0~1
WO~1~1""".split('\n'))])))
>>
*)
Notation "'0b10'" (* 2 (0x2) *)
  := (Const WO~1~0).
Notation "'0b11'" (* 3 (0x3) *)
  := (Const WO~1~1).
Notation "'0b1001'" (* 9 (0x9) *)
  := (Const WO~1~0~0~1).
Notation "'0b00010011'" (* 19 (0x13) *)
  := (Const WO~0~0~0~1~0~0~1~1).
Notation "'0b00011001'" (* 25 (0x19) *)
  := (Const WO~0~0~0~1~1~0~0~1).
Notation "'0b00011010'" (* 26 (0x1a) *)
  := (Const WO~0~0~0~1~1~0~1~0).
Notation "'0b00011011'" (* 27 (0x1b) *)
  := (Const WO~0~0~0~1~1~0~1~1).
Notation "'0b00011100'" (* 28 (0x1c) *)
  := (Const WO~0~0~0~1~1~1~0~0).
Notation "'0b00110011'" (* 51 (0x33) *)
  := (Const WO~0~0~1~1~0~0~1~1).
Notation "'0b00000001111111111111111111111111'" (* 33554431 (0x1ffffff) *)
  := (Const WO~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0b00000011111111111111111111111110'" (* 67108862 (0x3fffffe) *)
  := (Const WO~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0b00000011111111111111111111111111'" (* 67108863 (0x3ffffff) *)
  := (Const WO~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0b00000111111111111111111111011010'" (* 134217690 (0x7ffffda) *)
  := (Const WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1~0).
Notation "'0b00000111111111111111111111101110'" (* 134217710 (0x7ffffee) *)
  := (Const WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~1~0).
Notation "'0b00000111111111111111111111111110'" (* 134217726 (0x7fffffe) *)
  := (Const WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0b00000111111111111111111111111111'" (* 134217727 (0x7ffffff) *)
  := (Const WO~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0b00001111111111111111111111111110'" (* 268435454 (0xffffffe) *)
  := (Const WO~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0b00001111111111111111111111111111'" (* 268435455 (0xfffffff) *)
  := (Const WO~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0b00011111111111111111111111111010'" (* 536870906 (0x1ffffffa) *)
  := (Const WO~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~0).
Notation "'0b00011111111111111111111111111110'" (* 536870910 (0x1ffffffe) *)
  := (Const WO~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
Notation "'0b0000000000000111111111111111111111111111111111111111111111111111'" (* 2251799813685247 (0x7ffffffffffffL) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1).
Notation "'0b0000000000001111111111111111111111111111111111111111111111011010'" (* 4503599627370458 (0xfffffffffffdaL) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0~1~1~0~1~0).
Notation "'0b0000000000001111111111111111111111111111111111111111111111111110'" (* 4503599627370494 (0xffffffffffffeL) *)
  := (Const WO~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~0).
