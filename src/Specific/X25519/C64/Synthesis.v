Require Import Crypto.Specific.Framework.SynthesisFramework.
Require Import Crypto.Specific.X25519.C64.CurveParameters.

Module P <: PrePackage.
  Definition package : Tag.Context.
  Proof. make_Synthesis_package curve extra_prove_mul_eq extra_prove_square_eq. Defined.
End P.

Module Export S := PackageSynthesis P.
Import CurveParameters.Notations.
Arguments Hierarchy.ring : clear implicits.
Arguments Ring.is_homomorphism : clear implicits.
Import BinNums.
Import Arithmetic.Core.
Import P.
Import Program.
Import ModularArithmetic.
Open Scope F_scope.
Import BinInt.
Check ring.
Check m.
Locate to_pos.
Check B.Positional.eq.
Check B.Positional.Fencode _.
Locate xzladderstep.
Set Printing Implicit.
Check XZ.M.xzladderstep _ _ _.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.ExprInversion.
Print RawCurveParameters.CurveParameters.
Check ring.
Eval cbv [B.Positional.eq] in (@B.Positional.eq wt sz m).
Check Expr.
Notation Expr := (Expr Syntax.base_type Syntax.op).
Record SynthesisOutput (curve : RawCurveParameters.CurveParameters) :=
  {
    m := Z.to_pos (RawCurveParameters.s curve - B.Associational.eval (RawCurveParameters.c curve))%Z;
    rT := Syntax.tuple (Tbase (TWord (Z.to_nat (Z.log2_up bitwidth)))) (RawCurveParameters.sz curve);
    T' := interp_flat_type Syntax.interp_base_type rT;
    RT := Syntax.Arrow Unit rT;

    encode : F m -> Expr RT
    (*:= _*);
    decode : T' -> F m
    (*:= _*);
    zero : Expr RT;
    one : Expr RT;
    add : Expr (Syntax.Arrow (rT * rT) rT); (* does not include carry *)
    sub : Expr (Syntax.Arrow (rT * rT) rT); (* does not include carry *)
    mul : Expr (Syntax.Arrow (rT * rT) rT); (* includes carry *)
    square : Expr (Syntax.Arrow rT rT); (* includes carry *)
    opp : Expr (Syntax.Arrow rT rT); (* does not include carry *)
    carry : Expr (Syntax.Arrow rT rT);
    carry_add : Expr (Syntax.Arrow (rT * rT) rT)
    := fun var => Syntax.Abs (fun v => LetIn (invert_Abs (add var) v) (invert_Abs (carry var)) );
    carry_sub : Expr (Syntax.Arrow (rT * rT) rT)
    := fun var => Syntax.Abs (fun v => LetIn (invert_Abs (sub var) v) (invert_Abs (carry var)) );
    carry_opp : Expr (Syntax.Arrow rT rT)
    := fun var => Syntax.Abs (fun v => LetIn (invert_Abs (opp var) v) (invert_Abs (carry var)) );

    P : T' -> Prop;

    encode_correct : forall v, _;
    encode_sig := fun v => exist P (Syntax.Interp Syntax.interp_op (encode v) tt) (encode_correct v);

    (*zero_correct : zero = Syntax.Interp Syntax.interp_op (encode 0%F) tt; (* which equality to use here? *)
    one_correct : one = Syntax.Interp Syntax.interp_op (encode 1%F) tt;*)
    zero_sig := encode_sig 0%F;
    one_sig := encode_sig 1%F;

    opp_correct := _;


    T := { v : T' | P v };
    eqT : T -> T -> Prop
    := fun x y => eq (decode (proj1_sig x)) (decode (proj1_sig y));
    ring : @Hierarchy.ring
             T eqT zero_sig one_sig opp_sig carry_add carry_sub mul;
  }.


    T' := Syntax.interp_flat_type Syntax.interp_base_type rT;
    T := { v :
         |

  }.
    eqT : T -> T -> Prop;
    encode : F m -> T;
    decode : T -> F m;
    zero : _;
    one : _;
    opp : _;
    add : _;
    sub : _;
    mul : _;
    ring : @Hierarchy.ring T eqT zero one opp add sub mul;
    encode_homomorphism
    : @Ring.is_homomorphism
        (F m) eq 1 F.add F.mul
        T eqT one add mul
        encode;
    decode_homomorphism
    : @Ring.is_homomorphism
        T eqT one add mul
        (F m) eq 1 F.add F.mul
        decode;
    a24t : if RawCurveParameters.montgomery curve return Type then unit else T;
    xzladderstep : if RawCurveParameters.montgomery curve return Type then unit else (T -> T -> T * T -> T * T -> (T * T) * (T * T));
    xzladderstep_correct
    : (if RawCurveParameters.montgomery curve as mont
          return (if mont return Type then unit else T)
                 -> (if mont return Type then unit else (T -> T -> T * T -> T * T -> (T * T) * (T * T)))
                 -> Prop
       then fun _ _ => True
       else fun a24' xzladderstep
            => forall x1 Q Q',
                Tuple.fieldwise
                  (n:=2) (Tuple.fieldwise (n:=2) eq)
                  (Tuple.map (n:=2) (Tuple.map (n:=2) decode) (xzladderstep a24' x1 Q Q'))
                  (@XZ.M.xzladderstep (F m) F.add F.sub F.mul (F.of_Z m a24) (decode x1) (Tuple.map (n:=2) decode Q) (Tuple.map (n:=2) decode Q')))
        a24t xzladderstep

  }.
Record SynthesisOutput (curve : RawCurveParameters.CurveParameters) :=
  {
    m := Z.to_pos (RawCurveParameters.s curve - B.Associational.eval (RawCurveParameters.c curve))%Z;
    T : Type;
    eqT : T -> T -> Prop;
    encode : F m -> T;
    decode : T -> F m;
    zero : _;
    one : _;
    opp : _;
    add : _;
    sub : _;
    mul : _;
    ring : @Hierarchy.ring T eqT zero one opp add sub mul;
    encode_homomorphism
    : @Ring.is_homomorphism
        (F m) eq 1 F.add F.mul
        T eqT one add mul
        encode;
    decode_homomorphism
    : @Ring.is_homomorphism
        T eqT one add mul
        (F m) eq 1 F.add F.mul
        decode;
    a24t : if RawCurveParameters.montgomery curve return Type then unit else T;
    xzladderstep : if RawCurveParameters.montgomery curve return Type then unit else (T -> T -> T * T -> T * T -> (T * T) * (T * T));
    xzladderstep_correct
    : (if RawCurveParameters.montgomery curve as mont
          return (if mont return Type then unit else T)
                 -> (if mont return Type then unit else (T -> T -> T * T -> T * T -> (T * T) * (T * T)))
                 -> Prop
       then fun _ _ => True
       else fun a24' xzladderstep
            => forall x1 Q Q',
                Tuple.fieldwise
                  (n:=2) (Tuple.fieldwise (n:=2) eq)
                  (Tuple.map (n:=2) (Tuple.map (n:=2) decode) (xzladderstep a24' x1 Q Q'))
                  (@XZ.M.xzladderstep (F m) F.add F.sub F.mul (F.of_Z m a24) (decode x1) (Tuple.map (n:=2) decode Q) (Tuple.map (n:=2) decode Q')))
        a24t xzladderstep

  }.



ring
     : Hierarchy.ring (Z ^ sz) (B.Positional.eq wt m)
         (` zero_sig) (` one_sig) (` opp_sig) (` add_sig)
         (` sub_sig) (` mul_sig) /\
       Ring.is_homomorphism (F m) eq 1 F.add F.mul (Z ^ sz)
         (B.Positional.eq wt m) (` one_sig) (` add_sig)
         (` mul_sig) (B.Positional.Fencode wt) /\
       Ring.is_homomorphism (Z ^ sz) (B.Positional.eq wt m)
         (` one_sig) (` add_sig) (` mul_sig) (F m) eq 1 F.add F.mul
         (B.Positional.Fdecode wt)

P.ring
     : Hierarchy.ring (BinNums.Z ^ P.sz) (Core.B.Positional.eq P.wt P.m)
         (proj1_sig P.zero_sig) (proj1_sig P.one_sig)
         (proj1_sig P.opp_sig) (proj1_sig P.add_sig) (proj1_sig P.sub_sig)
         (proj1_sig P.mul_sig) /\
       Ring.is_homomorphism (ModularArithmetic.F.F P.m) eq ModularArithmetic.F.one
         ModularArithmetic.F.add ModularArithmetic.F.mul
         (BinNums.Z ^ P.sz) (Core.B.Positional.eq P.wt P.m)
         (proj1_sig P.one_sig) (proj1_sig P.add_sig) (proj1_sig P.mul_sig)
         (Core.B.Positional.Fencode P.wt) /\
       Ring.is_homomorphism (BinNums.Z ^ P.sz) (Core.B.Positional.eq P.wt P.m)
         (proj1_sig P.one_sig) (proj1_sig P.add_sig) (proj1_sig P.mul_sig)
         (ModularArithmetic.F.F P.m) eq ModularArithmetic.F.one
         ModularArithmetic.F.add ModularArithmetic.F.mul
         (Core.B.Positional.Fdecode P.wt)
