Require Import Coq.ZArith.BinIntDef.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Tuple.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.Linearize.
Require Import Crypto.Compilers.Eta.
Require Import Crypto.Compilers.LinearizeInterp.
Require Import Crypto.Compilers.EtaInterp.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Tuple.
Require Import Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
Require Import Crypto.Util.Notations.
Import CurveParameters.Notations.

Local Set Implicit Arguments.
Local Coercion Z.to_nat : Z >-> nat.
Local Notation interp_flat_type := (interp_flat_type interp_base_type).

Section gen.
  Context (curve : CurveParameters.CurveParameters).

  Local Notation wt := curve.(wt).
  Local Notation lgwt := curve.(lgwt).
  Local Notation m := curve.(m).
  Local Notation sz := curve.(sz).
  Local Notation bitwidth := curve.(bitwidth).

  Definition FencodeTuple := (@Positional.Fencode wt sz m (@modulo_cps) (@div_cps)).
  Definition FdecodeTuple : Z^sz -> F m
    := @Positional.Fdecode wt sz m.

  Section gen_base_type.
    Context (b : base_type).


    Definition rT := ((Tbase b)^sz)%ctype.
    Definition T' := (interp_flat_type rT).
    Definition RT := (Unit -> rT)%ctype.
    Definition encodeTuple : Z^sz -> Expr RT
      := fun v var
         => Abs
              (fun _
               => SmartPairf
                    (flat_interp_untuple
                       (T:=Tbase _)
                       (Tuple.map
                          (fun v => Op (OpConst v) TT)
                          v))).
    Definition decodeToTuple : T' -> Z^sz
      := fun v => Tuple.map interpToZ (flat_interp_tuple (T:=Tbase _) v).
    Definition encodeRaw : F m -> Expr RT
      := fun v => encodeTuple (FencodeTuple v).
    Definition decodeRaw : T' -> F m
      := fun v => FdecodeTuple (decodeToTuple v).
  End gen_base_type.

  Local Notation TW := (TWord (Z.log2_up bitwidth)).
  Local Notation tZ := (Tbase TZ).
  Local Notation tW := (Tbase TW).
  Local Notation RTZ := (RT TZ).
  Local Notation rTZ := (rT TZ).
  Local Notation RTW := (RT TW).
  Local Notation rTW := (rT TW).

  Local Notation η e := (ExprEta (Linearize e%expr)).
  Local Notation ηP P H := (InterpExprEta_ind P (InterpLinearize_ind (e:=(_ ∘ _)%expr) P H)).

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


  Record SynthesisOutputProps (b : base_type) :=
    {
      P_tight : T' b -> Prop;
      P_loose : T' b -> Prop;
      P_1 : interp_base_type b -> Prop;
      P_relax : forall v, P_tight v -> P_loose v;
    }.

  Definition True_SynthesisOutputProps {b} : SynthesisOutputProps b :=
    {|
      P_tight v := True;
      P_loose v := True;
      P_1 v := True;
      P_relax v pf := pf;
    |}.


  Record SynthesisOutputOpsValid
         {b} (ops : SynthesisOutputOps b) (P_ : SynthesisOutputProps b)
    :=
    {
      encode_valid : forall v, _;
      encode_correct : forall v, ops.(decode) (Interp (ops.(encode) v) tt) = v;
      encode_sig := fun v => exist P_.(P_tight) (Interp (ops.(encode) v) tt) (encode_valid v);

      decode_sig := fun v : sig P_.(P_tight) => ops.(decode) (proj1_sig v);

      zero_sig := encode_sig 0%F;
      one_sig := encode_sig 1%F;

      zero_correct
      : Interp ops.(zero) tt
        = Interp (ops.(encode) 0%F) tt;
      one_correct
      : Interp ops.(one) tt
        = Interp (ops.(encode) 1%F) tt;

      carry_valid : forall x, P_.(P_loose) x -> P_.(P_tight) (Interp ops.(carry) x);
      carry_correct : forall x, P_.(P_loose) x -> ops.(decode) (Interp ops.(carry) x) = ops.(decode) x;

      opp_valid : forall x, P_.(P_tight) x -> P_.(P_loose) (Interp ops.(opp) x);
      carry_opp_valid : forall x, P_.(P_tight) x -> P_.(P_tight) (Interp ops.(carry_opp) x)
      := fun x Px => ηP _ (@carry_valid _ (@opp_valid _ Px));
      carry_opp_sig := fun x => exist P_.(P_tight) _ (@carry_opp_valid (proj1_sig x) (proj2_sig x));

      add_valid : forall x y, P_.(P_tight) x -> P_.(P_tight) y -> P_.(P_loose) (Interp ops.(add) (x, y));
      carry_add_valid : forall x y, P_.(P_tight) x -> P_.(P_tight) y -> P_.(P_tight) (Interp ops.(carry_add) (x, y))
      := fun x y Px Py => ηP _ (@carry_valid _ (@add_valid _ _ Px Py));
      carry_add_sig := fun x y => exist P_.(P_tight) _ (@carry_add_valid (proj1_sig x) (proj1_sig y) (proj2_sig x) (proj2_sig y));

      sub_valid : forall x y, P_.(P_tight) x -> P_.(P_tight) y -> P_.(P_loose) (Interp ops.(sub) (x, y));
      carry_sub_valid : forall x y, P_.(P_tight) x -> P_.(P_tight) y -> P_.(P_tight) (Interp ops.(carry_sub) (x, y))
      := fun x y Px Py => ηP _ (@carry_valid _ (@sub_valid _ _ Px Py));
      carry_sub_sig := fun x y => exist P_.(P_tight) _ (@carry_sub_valid (proj1_sig x) (proj1_sig y) (proj2_sig x) (proj2_sig y));

      carry_mul_valid : forall x y, P_.(P_loose) x -> P_.(P_loose) y -> P_.(P_tight) (Interp ops.(carry_mul) (x, y));
      carry_mul_sig := fun x y => exist P_.(P_tight) _ (@carry_mul_valid (proj1_sig x) (proj1_sig y) (P_.(P_relax) _ (proj2_sig x)) (P_.(P_relax) _ (proj2_sig y)));

      carry_square_valid : forall x, P_.(P_loose) x -> P_.(P_tight) (Interp ops.(carry_square) x);
      carry_square_correct : forall x, P_.(P_loose) x -> ops.(decode) (Interp ops.(carry_square) x) = ops.(decode) (Interp ops.(carry_mul) (x, x));

      freeze_correct
      : curve.(CurveParameters.freeze) = true
        -> forall x,
          P_.(P_tight) x
          -> option_map (fun freeze : Expr (rT b -> rT b)
                         => ops.(decode) (Interp freeze x))
                        ops.(freeze)
             = Some (ops.(decode) x);
      freeze_valid
      : match ops.(freeze) with
        | Some freeze => forall x, P_.(P_tight) x -> P_.(P_tight) (Interp freeze x)
        | None => curve.(CurveParameters.freeze) = false
        end;

      nonzero_correct
      : curve.(montgomery) = true
        -> forall x,
          P_.(P_tight) x
          -> option_map (fun nonzero : Expr (rT b -> Tbase b)
                         => (interpToZ (Interp nonzero x) =? 0))
                        ops.(nonzero)
             = Some (if Decidable.dec (ops.(decode) x = F.of_Z m 0) then true else false);
      nonzero_valid
      : match ops.(nonzero) with
        | Some nonzero => forall x, P_.(P_tight) x -> P_.(P_1) (Interp nonzero x)
        | None => curve.(montgomery) = false
        end;
    }.

  Record SynthesisOutputOpsRing {b ops P_} (svalid : @SynthesisOutputOpsValid b ops P_) :=
    {
      T := { v : T' b | P_.(P_tight) v };
      eqT : T -> T -> Prop
      := fun x y => eq (ops.(decode) (proj1_sig x)) (ops.(decode) (proj1_sig y));
      ring : @Hierarchy.ring
               T eqT svalid.(zero_sig) svalid.(one_sig) svalid.(carry_opp_sig) svalid.(carry_add_sig) svalid.(carry_sub_sig) svalid.(carry_mul_sig);
      encode_homomorphism
      : @Ring.is_homomorphism
          (F m) eq 1%F F.add F.mul
          T eqT svalid.(one_sig) svalid.(carry_add_sig) svalid.(carry_mul_sig)
          svalid.(encode_sig);
      decode_homomorphism
      : @Ring.is_homomorphism
          T eqT svalid.(one_sig) svalid.(carry_add_sig) svalid.(carry_mul_sig)
          (F m) eq 1%F F.add F.mul
          svalid.(decode_sig);
    }.

  Record SynthesisOutput :=
    {
      opsZ : SynthesisOutputOps TZ;
      opsW : SynthesisOutputOps TW;

      P_Z : SynthesisOutputProps TZ;
      PZ_to_PW_map PZ
      := fun v => PZ (tuple_map (A:=Tbase TW) (B:=Tbase TZ) (SmartVarfMap (@interpToZ)) v);
      P_W : SynthesisOutputProps TW
      := {|
          P_tight := PZ_to_PW_map P_Z.(P_tight);
          P_loose := PZ_to_PW_map P_Z.(P_loose);
          P_1 := fun v => P_Z.(P_1) (interpToZ v);
          P_relax := fun v => P_Z.(P_relax) _
        |};

      opsZ_valid : SynthesisOutputOpsValid opsZ P_Z;
      opsW_valid : SynthesisOutputOpsValid opsW P_W;

      opsZ_ring : SynthesisOutputOpsRing opsZ_valid;
      opsW_ring : SynthesisOutputOpsRing opsW_valid;
    }.
End gen.

Section raw.
  Context (rcurve : RawCurveParameters.CurveParameters).

  Definition SynthesisPackage := SynthesisOutput (fill_defaults_CurveParameters rcurve).
End raw.

Ltac cbv_SynthesisOutputOps_projections :=
  cbv [encode
         decode
         zero
         one
         add
         sub
         carry_mul
         carry_square
         opp
         carry
         freeze
         nonzero
         carry_add
         carry_sub
         carry_opp].
