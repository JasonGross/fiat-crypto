(** * Interpretation of PHOAS syntax for expression trees on ℤ *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Reflection.Equality.
Require Import Crypto.Reflection.MapCastWithCastOp.
Require Import Crypto.ModularArithmetic.ModularBaseSystemListZOperations.
Require Import Crypto.Util.Equality.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Option.
Require Crypto.Util.Tuple.
Require Crypto.Util.HList.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.
Require Import Bedrock.Word.
Require Import Crypto.Util.WordUtil.
Export Reflection.Syntax.Notations.

Local Notation eta x := (fst x, snd x).
Local Notation eta3 x := (eta (fst x), snd x).
Local Notation eta4 x := (eta3 (fst x), snd x).

Module Import Bounds.
  Record bounds := { lower : Z ; upper : Z }.

  Bind Scope bounds_scope with bounds.
  Definition t := option bounds. (* TODO?: Separate out the bounds computation from the overflow computation? e.g., have [safety := in_bounds | overflow] and [t := bounds * safety]? *)
  Bind Scope bounds_scope with t.
  Local Coercion Z.of_nat : nat >-> Z.
  (*Definition wordWToBounds (x : WordW.wordW) : t
    := let v := WordW.wordWToZ x in Some {| lower := v ; upper := v |}.*)
  Definition SmartBuildBounds (l u : Z)
    := if ((0 <=? l) (*&& (Z.log2 u <? WordW.bit_width)*))%Z%bool
       then Some {| lower := l ; upper := u |}
       else None.
  Definition t_map1 (f : bounds -> bounds) (x : t)
    := match x with
       | Some x
         => match f x with
            | Build_bounds l u
              => SmartBuildBounds l u
            end
       | _ => None
       end%Z.
  Definition t_map2 (f : bounds -> bounds -> bounds) (x y : t)
    := match x, y with
       | Some x, Some y
         => match f x y with
            | Build_bounds l u
              => SmartBuildBounds l u
            end
       | _, _ => None
       end%Z.
  Definition t_map4 (f : bounds -> bounds -> bounds -> bounds -> bounds) (x y z w : t)
    := match x, y, z, w with
       | Some x, Some y, Some z, Some w
         => match f x y z w with
            | Build_bounds l u
              => SmartBuildBounds l u
            end
       | _, _, _, _ => None
       end%Z.
  Definition add' : bounds -> bounds -> bounds
    := fun x y => let (lx, ux) := x in let (ly, uy) := y in {| lower := lx + ly ; upper := ux + uy |}.
  Definition add : t -> t -> t := t_map2 add'.
  Definition sub' : bounds -> bounds -> bounds
    := fun x y => let (lx, ux) := x in let (ly, uy) := y in {| lower := lx - uy ; upper := ux - ly |}.
  Definition sub : t -> t -> t := t_map2 sub'.
  Definition mul' : bounds -> bounds -> bounds
    := fun x y => let (lx, ux) := x in let (ly, uy) := y in {| lower := lx * ly ; upper := ux * uy |}.
  Definition mul : t -> t -> t := t_map2 mul'.
  Definition shl' : bounds -> bounds -> bounds
    := fun x y => let (lx, ux) := x in let (ly, uy) := y in {| lower := lx << ly ; upper := ux << uy |}.
  Definition shl : t -> t -> t := t_map2 shl'.
  Definition shr' : bounds -> bounds -> bounds
    := fun x y => let (lx, ux) := x in let (ly, uy) := y in {| lower := lx >> uy ; upper := ux >> ly |}.
  Definition shr : t -> t -> t := t_map2 shr'.
  Definition land' : bounds -> bounds -> bounds
    := fun x y => let (lx, ux) := x in let (ly, uy) := y in {| lower := 0 ; upper := Z.min ux uy |}.
  Definition land : t -> t -> t := t_map2 land'.
  Definition lor' : bounds -> bounds -> bounds
    := fun x y => let (lx, ux) := x in let (ly, uy) := y in
                                       {| lower := Z.max lx ly;
                                          upper := 2^(Z.max (Z.log2_up (ux+1)) (Z.log2_up (uy+1))) - 1 |}.
  Definition lor : t -> t -> t := t_map2 lor'.
  Definition neg' (int_width : Z) : bounds -> bounds
    := fun v
       => let (lb, ub) := v in
          let might_be_one := ((lb <=? 1) && (1 <=? ub))%Z%bool in
          let must_be_one := ((lb =? 1) && (ub =? 1))%Z%bool in
          if must_be_one
          then {| lower := Z.ones int_width ; upper := Z.ones int_width |}
          else if might_be_one
               then {| lower := 0 ; upper := Z.ones int_width |}
               else {| lower := 0 ; upper := 0 |}.
  Definition neg (int_width : Z) : t -> t
    := fun v
       => if ((0 <=? int_width) (*&& (int_width <=? WordW.bit_width)*))%Z%bool
          then t_map1 (neg' int_width) v
          else None.
  Definition cmovne' (r1 r2 : bounds) : bounds
    := let (lr1, ur1) := r1 in let (lr2, ur2) := r2 in {| lower := Z.min lr1 lr2 ; upper := Z.max ur1 ur2 |}.
  Definition cmovne (x y r1 r2 : t) : t := t_map4 (fun _ _ => cmovne') x y r1 r2.
  Definition cmovle' (r1 r2 : bounds) : bounds
    := let (lr1, ur1) := r1 in let (lr2, ur2) := r2 in {| lower := Z.min lr1 lr2 ; upper := Z.max ur1 ur2 |}.
  Definition cmovle (x y r1 r2 : t) : t := t_map4 (fun _ _ => cmovle') x y r1 r2.

  Module Export Notations.
    Delimit Scope bounds_scope with bounds.
    Notation "b[ l ~> u ]" := {| lower := l ; upper := u |} : bounds_scope.
    Infix "+" := add : bounds_scope.
    Infix "-" := sub : bounds_scope.
    Infix "*" := mul : bounds_scope.
    Infix "<<" := shl : bounds_scope.
    Infix ">>" := shr : bounds_scope.
    Infix "&'" := land : bounds_scope.
  End Notations.

  Definition interp_base_type (ty : base_type) : Set := t.
  Definition interp_op {src dst} (f : op src dst) : interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst
    := match f in op src dst return interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst with
       | OpConst TZ v => fun _ => SmartBuildBounds v v
       | OpConst (TWord _) v => fun _ => SmartBuildBounds (FixedWordSizes.wordToZ v) (FixedWordSizes.wordToZ v)
       | Add _ => fun xy => fst xy + snd xy
       | Sub _ => fun xy => fst xy - snd xy
       | Mul _ => fun xy => fst xy * snd xy
       | Shl _ => fun xy => fst xy << snd xy
       | Shr _ => fun xy => fst xy >> snd xy
       | Land _ => fun xy => land (fst xy) (snd xy)
       | Lor _ => fun xy => lor (fst xy) (snd xy)
       | Neg _ int_width => fun x => neg int_width x
       | Cmovne _ => fun xyzw => let '(x, y, z, w) := eta4 xyzw in cmovne x y z w
       | Cmovle _ => fun xyzw => let '(x, y, z, w) := eta4 xyzw in cmovle x y z w
       | Cast _ _ => fun x => x
       end%bounds.

  (*Definition of_wordW ty : WordW.interp_base_type ty -> interp_base_type ty
      := match ty return WordW.interp_base_type ty -> interp_base_type ty with
         | TZ => wordWToBounds
         end.*)

  Ltac inversion_bounds :=
    let lower := (eval cbv [lower] in (fun x => lower x)) in
    let upper := (eval cbv [upper] in (fun y => upper y)) in
    repeat match goal with
           | [ H : _ = _ :> bounds |- _ ]
             => pose proof (f_equal lower H); pose proof (f_equal upper H); clear H;
                cbv beta iota in *
           | [ H : _ = _ :> t |- _ ]
             => unfold t in H; inversion_option
           end.

  Definition bounds_to_base_type' (b : bounds) : base_type
    := if (0 <=? lower b)%Z
       then TWord (Z.to_nat (Z.log2_up (Z.log2_up (1 + upper b))))
       else TZ.
  Definition bounds_to_base_type (b : t) : base_type
    := match b with
       | None => TZ
       | Some b' => bounds_to_base_type' b'
       end.

  Definition SmartCast_base {var A A'} (x : exprf base_type op (var:=var) (Tbase A))
    : exprf base_type op (var:=var) (Tbase A')
    := match base_type_eq_dec A A' with
       | left pf => match pf with
                    | eq_refl => x
                    end
       | right _ => Op (Cast _ A') x
       end.
  Definition PairCast {var A B A' B'} (x : exprf base_type op (var:=var) (Tbase A * Tbase B))
    : exprf base_type op (var:=var) (Tbase A' * Tbase B')
    := match x in exprf _ _ T'
             return exprf base_type op (Tbase A' * Tbase B')%ctype
                    -> exprf base_type op (Tbase A' * Tbase B')%ctype
       with
       | Pair (Tbase A0) x1 (Tbase B0) x2
         => fun _ => Pair (SmartCast_base x1) (SmartCast_base x2)
       | _ => fun x => x
       end (LetIn x (fun xy => Pair (SmartCast_base (Var (fst xy))) (SmartCast_base (Var (snd xy))))).

  Definition bound_op {var}
             {src1 dst1 src2 dst2}
             (opc1 : op src1 dst1)
             (opc2 : op src2 dst2)
    : forall (args2 : exprf base_type op (var:=interp_base_type) src2),
      option
        { new_src : flat_type base_type
                    & exprf base_type op (var:=var) new_src
                    -> exprf base_type op (var:=var)
                             (SmartFlatTypeMap2
                                (fun t v => Tbase (bounds_to_base_type v))
                                (interpf (@interp_op) (Op opc2 args2))) }
    := match opc1, opc2 in op src2 dst2
             return (forall args2 : exprf base_type op (var:=interp_base_type) src2,
                        option { new_src : _
                                           & exprf base_type op (var:=var) new_src
                                           -> exprf base_type op (var:=var)
                                                    (SmartFlatTypeMap2
                                                       (fun t v => Tbase (bounds_to_base_type v))
                                                       (interpf (@interp_op) (@Op base_type op _ src2 dst2 opc2 args2))) })
       with
       | OpConst _ v, OpConst _ bs
         => fun args2
            => option_map
                 (fun bounds => existT (fun new_src => exprf _ _ new_src -> _)
                                       Unit
                                       (fun TT => SmartCast_base (Op (OpConst v) TT)))
                 (interpf (@interp_op) (Op (OpConst bs) args2))
       | Add T1, Add T2 => fun _ => Some (existT _ _ (Op (Add _)))
       | Sub T1, Sub T2 as opc2'
         => fun args2
            => let Targs' := (SmartFlatTypeMap2
                                (fun t v => Tbase (bounds_to_base_type v))
                                (interpf (@interp_op) args2)) in
               let TR := bounds_to_base_type (interpf (@interp_op) (Op opc2' args2) (t:=Tbase _)) in
               let Targ' : base_type
                   := match Targs' return match Targs' with Prod (Tbase _) (Tbase _) => base_type | _ => unit end with
                      | Prod (Tbase A) (Tbase B) => base_type_max A B
                      | _ => tt
                      end in
               let T := base_type_max Targ' TR in
               let AT := bounds_to_base_type (fst (interpf (@interp_op) args2)) in
               let BT := bounds_to_base_type (snd (interpf (@interp_op) args2)) in
               Some (if base_type_beq T TR
                        return { new_src : _
                                           & exprf base_type op new_src
                                           -> exprf base_type op (SmartFlatTypeMap2
                                                                    (fun t v => Tbase (bounds_to_base_type v))
                                                                    (interpf (@interp_op) (Op opc2' args2))) }
                     then existT _ _ (Op (Sub _))
                     else if flat_type_beq _ base_type_beq Targs' (Tbase T * Tbase T)%ctype
                          then existT _
                                      (Tbase T * Tbase T)%ctype
                                      (fun x => Op (Cast T TR) (Op (Sub T) x))
                          else existT
                                 (fun new_src : _
                                  => exprf _ op new_src
                                     -> exprf _ op (SmartFlatTypeMap2
                                                      (fun t v => Tbase (bounds_to_base_type v))
                                                      (interpf (@interp_op) (Op opc2' args2))))
                                 Targs'
                                 (fun x => Op (Cast T TR) (Op (Sub T) (PairCast (A:=AT) (B:=BT) x))))
       | Mul T1, Mul T2 => fun _ => Some (existT _ _ (Op (Mul _)))
       | Shl T1, Shl T2 => fun _ => Some (existT _ _ (Op (Shl _)))
       | Shr T1, Shr T2 as opc2'
         => fun args2
            => let Targs' := (SmartFlatTypeMap2
                                (fun t v => Tbase (bounds_to_base_type v))
                                (interpf (@interp_op) args2)) in
               let TR := bounds_to_base_type (interpf (@interp_op) (Op opc2' args2) (t:=Tbase _)) in
               let Targ' : base_type
                   := match Targs' return match Targs' with Prod (Tbase _) (Tbase _) => base_type | _ => unit end with
                      | Prod (Tbase A) (Tbase B) => base_type_max A B
                      | _ => tt
                      end in
               let T := base_type_max Targ' TR in
               let AT := bounds_to_base_type (fst (interpf (@interp_op) args2)) in
               let BT := bounds_to_base_type (snd (interpf (@interp_op) args2)) in
               Some (if base_type_beq T TR
                        return { new_src : _
                                           & exprf _ op new_src
                                           -> exprf _ op (SmartFlatTypeMap2
                                                            (fun t v => Tbase (bounds_to_base_type v))
                                                            (interpf (@interp_op) (Op opc2' args2))) }
                     then existT _ _ (Op (Shr _))
                     else if flat_type_beq _ base_type_beq Targs' (Tbase T * Tbase T)%ctype
                          then existT _
                                      (Tbase T * Tbase T)%ctype
                                      (fun x => Op (Cast T TR) (Op (Shr T) x))
                          else existT
                                 (fun new_src : _
                                  => exprf _ op new_src
                                     -> exprf _ op (SmartFlatTypeMap2
                                                      (fun t v => Tbase (bounds_to_base_type v))
                                                      (interpf (@interp_op) (Op opc2' args2))))
                                 Targs'
                                 (fun x => Op (Cast T TR) (Op (Shr T) (PairCast (A:=AT) (B:=BT) x))))
       | Land T1, Land T2 => fun _ => Some (existT _ _ (Op (Land _)))
       | Lor T1, Lor T2 => fun _ => Some (existT _ _ (Op (Lor _)))
       | Neg T1 int_width1, Neg T2 int_width2
         => fun _ => if Z.eqb int_width1 int_width2
                     then Some (existT _ _ (Op (Neg _ int_width1)))
                     else None
       | Cmovne T1, Cmovne T2 => fun _ => Some (existT _ _ (Op (Cmovne _)))
       | Cmovle T1, Cmovle T2 => fun _ => Some (existT _ _ (Op (Cmovle _)))
       | Cast A1 B1, Cast A2 B2 => fun _ => Some (existT _ _ (fun x => x))
       | OpConst _ _, _
       | Add _, _
       | Sub _, _
       | Mul _, _
       | Shl _, _
       | Shr _, _
       | Land _, _
       | Lor _, _
       | Neg _ _, _
       | Cmovne _, _
       | Cmovle _, _
       | Cast _ _, _
         => fun _ => None
       end.
  Definition ZToBounds (z : Z) : bounds := {| lower := z ; upper := z |}.
  Definition of_Z (z : Z) : t := Some (ZToBounds z).

  Definition of_interp t (z : Syntax.interp_base_type t) : interp_base_type t
    := Some (ZToBounds (match t return Syntax.interp_base_type t -> Z with
                        | TZ => fun z => z
                        | TWord logsz => FixedWordSizes.wordToZ
                        end z)).

  Definition MapBounds {t} (e : Expr base_type op t) input_bounds
    : Expr
        base_type op
        (MapCast.new_type (fun _ => bounds_to_base_type) input_bounds
                          (Interp (@interp_op) e))
    := @MapInterpCastWithCastOp
         base_type Bounds.interp_base_type
         op (@Bounds.interp_op)
         base_type_beq internal_base_type_dec_bl (fun _ t => Op (OpConst (ZToInterp 0)) TT)
         (fun _ => Bounds.bounds_to_base_type)
         (fun _ _ _ => Op (Cast _ _))
         (fun _ _ opc => match opc with Cast _ _ => true | _ => false end)
         (@Bounds.bound_op)
         _ e input_bounds.
  Definition ComputeBounds {t} (e : Expr base_type op t)
             (input_bounds : interp_flat_type interp_base_type (domain t))
    : interp_flat_type interp_base_type (codomain t)
    := Interp (@interp_op) e input_bounds.

  (*Definition mapf_interpToZ_T (T : flat_type base_type) : flat_type base_type
    :=
*)
  Definition mapf_interpToZ {T} : interp_flat_type Syntax.interp_base_type T -> interp_flat_type (fun _ => Z) T
    := SmartVarfMap (fun _ => interpToZ).

  Fixpoint Zis_bounded_by {T1 T2} : interp_flat_type (fun _ : base_type => Z) T1 -> interp_flat_type interp_base_type T2 -> bool
    := match T1, T2 return interp_flat_type (fun _ => Z) T1 -> interp_flat_type interp_base_type T2 -> bool with
       | Tbase T1, Tbase T2
         => fun val bounds
            => match bounds with
               | Some bounds'
                 => (lower bounds' <=? val) && (val <=? upper bounds')
               | None => false
               end
       | Unit, Unit => fun _ _ => true
       | Prod A1 B1, Prod A2 B2
         => fun x y => @Zis_bounded_by A1 A2 (fst x) (fst y) && @Zis_bounded_by B1 B2 (snd x) (snd y)
       | Unit, _
       | Tbase _, _
       | Prod _ _, _
         => fun _ _ => false
       end%bool%Z.
  Definition is_bounded_by {T1 T2} : interp_flat_type Syntax.interp_base_type T1 -> interp_flat_type interp_base_type T2 -> bool
    := fun x y => Zis_bounded_by (mapf_interpToZ x) y.
(*
  Definition is_bounded_and_correct {T1 T2 TB}
             (interpreted_val : interp_flat_type Syntax.interp_base_type T1)
             (orig_val : interp_flat_type Syntax.interp_base_type T2)
             (bounds : interp_flat_type interp_base_type TB)
    : Prop
    := mapf_interpToZ interpreted_val = orig_val

  (((Tuple.map (n:=k) fe25519WToZ irop = op)
       /\ HList.hlistP (fun v => is_bounded v = true) (Tuple.map (n:=k) fe25519WToZ irop))%type)*)
End Bounds.
