Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Tuple.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
Require Import Crypto.Specific.Framework.OutputType.
Require Import Crypto.Util.Notations.
Import CurveParameters.Notations.

Local Coercion Z.to_nat : Z >-> nat.
Local Notation interp_flat_type := (interp_flat_type interp_base_type).

Section with_curve.
  Context (curve : RawCurveParameters.CurveParameters).

  Local Notation RT := (RT curve).
  Local Notation rT := (rT curve).
  Local Notation T' := (T' curve).
  Local Notation encode := (encode curve).
  Local Notation decode := (decode curve).

  Record SynthesisPreOutput :=
    {
      zero : Expr RT;
      one : Expr RT;
      add : Expr (rT * rT -> rT); (* does not include carry *)
      sub : Expr (rT * rT -> rT); (* does not include carry *)
      mul : Expr (rT * rT -> rT); (* includes carry *)
      square : Expr (rT -> rT); (* includes carry *)
      opp : Expr (rT -> rT); (* does not include carry *)
      carry : Expr (rT -> rT);
      carry_add : Expr (rT * rT -> rT)
      := (carry ∘ add)%expr;
      carry_sub : Expr (rT * rT -> rT)
      := (carry ∘ sub)%expr;
      carry_opp : Expr (rT -> rT)
      := (carry ∘ opp)%expr;

      P : T' -> Prop;

      encode_valid : forall v, P (Interp (encode v) tt);

      zero_correct : zero = encode 0%F; (* which equality to use here? *)
      one_correct : one = encode 1%F; (* which equality to use here? *)

      opp_valid : forall x, P x -> P (Interp carry_opp x);
      add_valid : forall x y, P x -> P y -> P (Interp carry_add (x, y));
      sub_valid : forall x y, P x -> P y -> P (Interp carry_sub (x, y));
      mul_valid : forall x y, P x -> P y -> P (Interp mul (x, y));
      square_correct : forall x, P x -> Interp square x = Interp mul (x, x);
    }.

  Definition FinalizeOutput (v : SynthesisPreOutput) : SynthesisOutput curve.
  Proof.
    simple refine (let ring_goal : _ /\ _ /\ _ := _ in _); [ shelve.. | | ]; cycle 1.
    simple refine {|
             OutputType.zero := v.(zero);
             OutputType.one := v.(one);
             OutputType.add := v.(add);
             OutputType.sub := v.(sub);
             OutputType.mul := v.(mul);
             OutputType.opp := v.(opp);
             OutputType.carry := v.(carry);
             OutputType.square := v.(square);

             OutputType.zero_correct := v.(zero_correct);
             OutputType.one_correct := v.(one_correct);
             OutputType.encode_valid := v.(encode_valid);
             OutputType.add_valid := v.(add_valid);
             OutputType.sub_valid := v.(sub_valid);
             OutputType.mul_valid := v.(mul_valid);
             OutputType.opp_valid := v.(opp_valid);
             OutputType.square_correct := v.(square_correct);

             OutputType.ring := proj1 ring_goal;
             OutputType.encode_homomorphism := proj1 (proj2 ring_goal);
             OutputType.decode_homomorphism := proj2 (proj2 ring_goal);
           |}.
    { intro x; cbv [decode encode Interp interp].
      lazymatch goal with
      | [ |- context G[flat_interp_untuple (Tuple.map ?f ?x)] ]
          let G' := context[tuple_map f x]
      SearchAbout interpf SmartPairf.
    constructor.
