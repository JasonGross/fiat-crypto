(*Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Eta.
Require Import Crypto.Compilers.Linearize.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.EtaInterp.
Require Import Crypto.Compilers.LinearizeInterp.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Specific.Framework.OutputType.
Require Import Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Ladderstep.

Local Set Implicit Arguments.

Section with_curve.
  Context (curve : CurveParameters.CurveParameters).

  Local Notation m := curve.(m).
  Local Notation sz := curve.(sz).
  Local Notation bitwidth := curve.(bitwidth).
  Local Notation TW := (TWord (Z.log2_up bitwidth)).
  Local Notation tZ := (Tbase TZ).
  Local Notation tW := (Tbase TW).
  Local Notation RT := curve.(RT).
  Local Notation rT := curve.(rT).
  Local Notation RTZ := (RT TZ).
  Local Notation rTZ := (rT TZ).
  Local Notation RTW := (RT TW).
  Local Notation rTW := (rT TW).
  Local Notation rT4 b := ((rT b * rT b) * (rT b * rT b))%ctype.
  Local Notation RT4 b := (Unit -> rT4 b)%ctype.
  Local Notation exprfT b := (exprf base_type op (rT b)).
  Local Notation exprfT4 b := (exprf base_type op (rT4 b)).
  Local Notation ExprT4 b := (Expr (RT4 b)).

  Section with_ops.
    Context (b : base_type)
            (ops : SynthesisOutputOps curve b).

    Definition xzladderstepf var a24 x1 Q Q'
      := @Mxzladderstep_cps
           (exprfT b) (exprfT b) (exprfT4 b)
           id (* relax *)
           (fun x f => LetIn x (fun x => f (SmartVarf x)))
           (fun x f => LetIn x (fun x => f (SmartVarf x)))
           (fun x y => LetIn (x, y)%expr (invert_Abs (ops.(add) var)))
           (fun x y => LetIn (x, y)%expr (invert_Abs (ops.(sub) var)))
           (fun x y => LetIn (x, y)%expr (invert_Abs (ops.(carry_mul) var)))
           (fun x => LetIn x (invert_Abs (ops.(carry_square) var)))
           (fun '((x, y), (z, w)) => ((x, y), (z, w))%expr)
           a24 x1 Q Q'.

    Definition xzladderstep : Expr (rT b * rT b * (rT4 b) -> rT4 b)
      := ExprEta (Linearize
               (invert_Abs (ops.(encode) (F.of_Z m a24) var)

                           Definition xzladderstepf_with_a24
      := fun var
         => option_map
              (fun a24 => xzladderstepf (invert_Abs (ops.(encode) (F.of_Z m a24) var) tt))
              curve.(a24).




Check xzladderstepf_with_a24.
    Check ops.(add).
                                 (fun x => f (Smart
             _).
      Context (relax : T_tight -> T_loose)
          (let_inT : T_tight -> (T_tight -> retT) -> retT)
          (let_inL : T_loose -> (T_loose -> retT) -> retT)
          (add sub : T_tight -> T_tight -> T_loose)
          (carry_mul : T_loose -> T_loose -> T_tight)
          (carry_square : T_loose -> T_tight)
          (cont : preretT -> retT).






      Record SynthesisOutputOps (b : base_type) :=
    {
      encodeZ : F m -> Z^sz;
      decodeZ : Z^sz -> F m;
      encode : F m -> Expr (RT b)
      := fun v => encodeTuple b (encodeZ v);
      decode : T' b -> F m
      := fun v => decodeZ (decodeToTuple b v);
      zero : Expr (RT b);
      one : Expr (RT b);
      add : Expr (rT b * rT b -> rT b); (* does not include carry *)
      sub : Expr (rT b * rT b -> rT b); (* does not include carry *)
      carry_mul : Expr (rT b * rT b -> rT b); (* includes carry *)
      carry_square : Expr (rT b -> rT b); (* includes carry *)
      opp : Expr (rT b -> rT b); (* does not include carry *)
      carry : Expr (rT b -> rT b);
      freeze : option (Expr (rT b -> rT b)); (* TODO: what's the relation, if any between freeze and nonzero? *)
      nonzero : option (Expr (rT b -> Tbase b));
      carry_add : Expr (rT b * rT b -> rT b)
      := η (carry ∘ add);
      carry_sub : Expr (rT b * rT b -> rT b)
      := η (carry ∘ sub);
      carry_opp : Expr (rT b -> rT b)
      := η (carry ∘ opp);
    }.

  About SynthesisOutput.
*)
