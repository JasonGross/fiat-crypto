Require Import Coq.ZArith.BinIntDef.
Require Import Coq.omega.Omega.
Require Import Coq.micromega.Lia.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Tuple.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.Z.Bounds.Interpretation.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Tuple.
Require Import Crypto.Util.SideConditions.CorePackages.
Require Import Crypto.Util.SideConditions.ReductionPackages.
Require Import Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
Require Import Crypto.Specific.Framework.OutputType.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.ListUtil.
Import CurveParameters.Notations.

Local Set Implicit Arguments.
Local Coercion Z.to_nat : Z >-> nat.
Local Notation interp_flat_type := (interp_flat_type interp_base_type).

Section gen.
  Context (curve : CurveParameters.CurveParameters)
          (ropsZ : SynthesisOutputOps curve TZ)
          (P_extra : SynthesisOutputProps curve TZ).

  Local Notation wt := curve.(wt).
  Local Notation lgwt := curve.(lgwt).
  Local Notation m := curve.(m).
  Local Notation sz := curve.(sz).
  Local Notation bitwidth := curve.(bitwidth).
  Local Notation allowable_bit_widths := curve.(allowable_bit_widths).
  Local Notation freeze_allowable_bit_widths := curve.(freeze_allowable_bit_widths).
  Local Notation bounds_tight := curve.(bounds_tight).
  Local Notation bounds_loose := curve.(bounds_loose).
  Local Notation bounds_limb_widths := curve.(bounds_limb_widths).
  Local Notation bound1 := curve.(bound1).

  Local Notation TW := (TWord (Z.log2_up bitwidth)).
  Local Notation tZ := (Tbase TZ).
  Local Notation tW := (Tbase TW).
  Local Notation RT := (curve.(RT)).
  Local Notation rT := (curve.(rT)).
  Local Notation RTZ := (RT TZ).
  Local Notation rTZ := (rT TZ).
  Local Notation RTW := (RT TW).
  Local Notation rTW := (rT TW).
  Local Notation T' := curve.(T').
  Local Notation decodeZ := ropsZ.(decode).
  Local Notation encodeZ := ropsZ.(encode).
  Local Notation carryZ := ropsZ.(carry).
  Local Notation addZ := ropsZ.(add).
  Local Notation subZ := ropsZ.(sub).
  Local Notation oppZ := ropsZ.(opp).
  Local Notation carry_mulZ := ropsZ.(carry_mul).

  Local Notation allowable_lgsz := (List.map Nat.log2 allowable_bit_widths).

  Local Notation pick_typeb := (@Interpretation.Bounds.bounds_to_base_type (Interpretation.Bounds.round_up_to_in_list allowable_lgsz)) (only parsing).
  Local Notation pick_type v := (SmartFlatTypeMap pick_typeb v).

  Definition bounds_tightZ :=
    flat_interp_untuple
      (interp_base_type:=Interpretation.Bounds.interp_base_type)
      (T:=Tbase TZ)
      bounds_tight.
  Definition bounds_looseZ :=
    flat_interp_untuple
      (interp_base_type:=Interpretation.Bounds.interp_base_type)
      (T:=Tbase TZ)
      bounds_loose.

  Local Notation exprT n
    := (fun b : base_type => ((rT b)^n%nat -> (rT b))%ctype).
  Local Notation exprT1 n
    := (fun b : base_type => ((rT b)^n%nat -> Tbase b)%ctype).

  Local Notation is_tight' a
    := (ZRange.is_bounded_by None bounds_tight a)
         (only parsing).
  Local Notation is_tight a
    := (is_tight' (flat_interp_tuple a))
         (only parsing).
  Local Notation is_loose a
    := (ZRange.is_bounded_by None bounds_loose (flat_interp_tuple a))
         (only parsing).

  Record BoundsInputSideConditions :=
    {
      decode_carry_oppZ
      : forall a : T' TZ,
        is_tight a
        -> P_extra.(P_tight) a
        -> decodeZ (Interp (carryZ ∘ oppZ)%expr a) = F.opp (decodeZ a);

      decode_carry_addZ
      : forall a b : T' TZ,
          is_tight a
          -> is_tight b
          -> P_extra.(P_tight) a
          -> P_extra.(P_tight) b
          -> decodeZ (Interp (carryZ ∘ addZ)%expr (a, b)) = (decodeZ a + decodeZ b)%F;

      decode_carry_subZ
      : forall a b : T' TZ,
          is_tight a
          -> is_tight b
          -> P_extra.(P_tight) a
          -> P_extra.(P_tight) b
          -> decodeZ (Interp (carryZ ∘ subZ)%expr (a, b)) = (decodeZ a - decodeZ b)%F;

      decode_carry_mulZ
      : forall a b : T' TZ,
          is_tight a
          -> is_tight b
          -> P_extra.(P_tight) a
          -> P_extra.(P_tight) b
          -> decodeZ (Interp carry_mulZ (a, b)) = (decodeZ a * decodeZ b)%F;
    }.

  Local Notation Fencode := (@Positional.Fencode wt sz m (@modulo_cps) (@div_cps)).
  Record SynthesisOutputOpsValid' (P_:=P_extra) (b:=TZ) :=
    {
      encode_bounded : forall v, ZRange.is_bounded_by None bounds_tight (ropsZ.(OutputType.encodeZ) v);
      decode_encode_correct
      : forall v, ropsZ.(OutputType.decodeZ) (ropsZ.(OutputType.encodeZ) v) = v;
      encode_valid : forall v, P_.(P_tight) (flat_interp_untuple (T:=Tbase TZ) (ropsZ.(OutputType.encodeZ) v));

      zero_correct
      : Interp ropsZ.(zero) tt
        = Interp (ropsZ.(encode) 0%F) tt;
      one_correct
      : Interp ropsZ.(one) tt
        = Interp (ropsZ.(encode) 1%F) tt;


      carry_valid : forall x, P_.(P_loose) x -> is_loose x -> P_.(P_tight) (Interp ropsZ.(carry) x);
      carry_correct : forall x, P_.(P_loose) x -> is_loose x -> ropsZ.(decode) (Interp ropsZ.(carry) x) = ropsZ.(decode) x;

      opp_valid : forall x, P_.(P_tight) x -> is_tight x -> P_.(P_loose) (Interp ropsZ.(opp) x);

      add_valid : forall x y, P_.(P_tight) x -> is_tight x -> P_.(P_tight) y -> is_tight y -> P_.(P_loose) (Interp ropsZ.(add) (x, y));

      sub_valid : forall x y, P_.(P_tight) x -> is_tight x -> P_.(P_tight) y -> is_tight y -> P_.(P_loose) (Interp ropsZ.(sub) (x, y));

      carry_mul_valid : forall x y, P_.(P_loose) x -> is_loose x -> P_.(P_loose) y -> is_loose y -> P_.(P_tight) (Interp ropsZ.(carry_mul) (x, y));

      carry_square_valid : forall x, P_.(P_loose) x -> is_loose x -> P_.(P_tight) (Interp ropsZ.(carry_square) x);
      carry_square_correct : forall x, P_.(P_loose) x -> is_loose x -> ropsZ.(decode) (Interp ropsZ.(carry_square) x) = ropsZ.(decode) (Interp ropsZ.(carry_mul) (x, x));

      freeze_correct
      : curve.(CurveParameters.freeze) = true
        -> forall x,
          P_.(P_tight) x
          -> is_tight x
          -> option_map (fun freeze : Expr (rT b -> rT b)
                         => ropsZ.(decode) (Interp freeze x))
                        ropsZ.(freeze)
             = Some (ropsZ.(decode) x);
      freeze_valid
      : match ropsZ.(freeze) with
        | Some freeze => forall x, P_.(P_tight) x -> is_tight x -> P_.(P_tight) (Interp freeze x)
        | None => curve.(CurveParameters.freeze) = false
        end;

      nonzero_correct
      : curve.(montgomery) = true
        -> forall x,
          P_.(P_tight) x
          -> is_tight x
          -> option_map (fun nonzero : Expr (rT b -> Tbase b)
                         => (interpToZ (Interp nonzero x) =? 0))
                        ropsZ.(nonzero)
             = Some (if Decidable.dec (ropsZ.(decode) x = F.of_Z m 0) then true else false);
      nonzero_valid
      : match ropsZ.(nonzero) with
        | Some nonzero => forall x, P_.(P_tight) x -> is_tight x -> P_.(P_1) (Interp nonzero x)
        | None => curve.(montgomery) = false
        end;
    }.
End gen.
