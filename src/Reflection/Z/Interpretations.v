(** * Interpretation of PHOAS syntax for expression trees on ℤ *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Z.Syntax.Util.
Require Import Crypto.Reflection.Z.OpInversion.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.InterpWfRel.
Require Import Crypto.Reflection.WfProofs.
Require Import Crypto.Reflection.WfInversion.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Reflection.TypeInversion.
Require Import Crypto.Reflection.Linearize.
Require Import Crypto.Reflection.LinearizeInterp.
Require Import Crypto.Reflection.LinearizeWf.
Require Import Crypto.Reflection.Inline.
Require Import Crypto.Reflection.InlineInterp.
Require Import Crypto.Reflection.Equality.
Require Import Crypto.Reflection.MapCast.
Require Import Crypto.Reflection.MapCastInterp.
Require Import Crypto.Reflection.MapCastWf.
Require Import Crypto.Reflection.Eta.
Require Import Crypto.Reflection.EtaInterp.
Require Import Crypto.ModularArithmetic.ModularBaseSystemListZOperations.
Require Import Crypto.Util.Equality.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Option.
Require Crypto.Util.Tuple.
Require Crypto.Util.HList.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.
Require Import Bedrock.Word.
Require Import Crypto.Util.WordUtil.
Require Import Crypto.Util.FixedWordSizesEquality.
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
  Section with_bitwidth.
    Context (bit_width : option Z).
    Definition SmartBuildBounds (l u : Z)
      := if ((0 <=? l) && (match bit_width with Some bit_width => Z.log2 u <? bit_width | None => true end))%Z%bool
         then Some {| lower := l ; upper := u |}
         else None.
    Definition SmartRebuildBounds (b : t) : t
      := match b with
         | Some b => SmartBuildBounds (lower b) (upper b)
         | None => None
         end.
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
  End with_bitwidth.

  Module Export Notations.
    Delimit Scope bounds_scope with bounds.
    Notation "b[ l ~> u ]" := {| lower := l ; upper := u |}
                              (format "b[ l  ~>  u ]") : bounds_scope.
    Infix "+" := (add _) : bounds_scope.
    Infix "-" := (sub _) : bounds_scope.
    Infix "*" := (mul _) : bounds_scope.
    Infix "<<" := (shl _) : bounds_scope.
    Infix ">>" := (shr _) : bounds_scope.
    Infix "&'" := (land _) : bounds_scope.
  End Notations.

  Definition interp_base_type (ty : base_type) : Set := t.

  Definition bit_width_of_base_type ty : option Z
    := match ty with
       | TZ => None
       | TWord logsz => Some (Z.of_nat (2^logsz))
       end.

  Definition interp_op {src dst} (f : op src dst) : interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst
    := match f in op src dst return interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst with
       | OpConst TZ v => fun _ => SmartBuildBounds None v v
       | OpConst (TWord _ as T) v => fun _ => SmartBuildBounds (bit_width_of_base_type T) (FixedWordSizes.wordToZ v) (FixedWordSizes.wordToZ v)
       | Add T => fun xy => add (bit_width_of_base_type T) (fst xy) (snd xy)
       | Sub T => fun xy => sub (bit_width_of_base_type T) (fst xy) (snd xy)
       | Mul T => fun xy => mul (bit_width_of_base_type T) (fst xy) (snd xy)
       | Shl T => fun xy => shl (bit_width_of_base_type T) (fst xy) (snd xy)
       | Shr T => fun xy => shr (bit_width_of_base_type T) (fst xy) (snd xy)
       | Land T => fun xy => land (bit_width_of_base_type T) (fst xy) (snd xy)
       | Lor T => fun xy => lor (bit_width_of_base_type T) (fst xy) (snd xy)
       | Neg T int_width => fun x => neg (bit_width_of_base_type T) int_width x
       | Cmovne T => fun xyzw => let '(x, y, z, w) := eta4 xyzw in cmovne (bit_width_of_base_type T) x y z w
       | Cmovle T => fun xyzw => let '(x, y, z, w) := eta4 xyzw in cmovle (bit_width_of_base_type T) x y z w
       | Cast _ T => fun x => SmartRebuildBounds (bit_width_of_base_type T) x
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
  Definition bounds2_to_base_type (b : t * t) : base_type
    := base_type_max (bounds_to_base_type (fst b)) (bounds_to_base_type (snd b)).
  Definition bounds3_to_base_type (b : t * t) (ex : t) : base_type
    := base_type_max (bounds2_to_base_type b) (bounds_to_base_type ex).
  Definition bounds4_to_base_type (b : t * t * t * t) : base_type
    := base_type_max (bounds2_to_base_type (fst (fst b))) (bounds2_to_base_type (snd (fst b), snd b)).
  Definition bounds5_to_base_type (b : t * t * t * t) (ex : t) : base_type
    := base_type_max (bounds4_to_base_type b) (bounds_to_base_type ex).

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
  Fixpoint SmartPairCast {var A A'} (x : exprf base_type op (var:=var) A)
    : option (exprf base_type op (var:=var) A')
    := match A, A' return exprf _ _ A -> option (exprf _ _ A') -> option (exprf _ _ A') with
       | Tbase _, Tbase _
         => fun x _ => Some (SmartCast_base x)
       | _, _
         => fun _ v => v
       end
         x
         (match x, A' return option (exprf _ _ A') with
          | Pair _ x1 _ x2, Prod _ _
            => match @SmartPairCast _ _ _ x1, @SmartPairCast _ _ _ x2 with
               | Some v1, Some v2 => Some (Pair v1 v2)
               | _, _ => None
               end
          | _, _ => None
          end).
  Definition QuadCast {var A B C D A' B' C' D'} (x : exprf base_type op (var:=var) (Tbase A * Tbase B * Tbase C * Tbase D))
    : exprf base_type op (var:=var) (Tbase A' * Tbase B' * Tbase C' * Tbase D')
    := match SmartPairCast x with
       | Some v => v
       | None
         => LetIn x (fun xyzw => SmartPairf (t:=Tbase A' * Tbase B' * Tbase C' * Tbase D')
                                            (SmartCast_base (Var (fst (fst (fst xyzw)))),
                                             SmartCast_base (Var (snd (fst (fst xyzw)))),
                                             SmartCast_base (Var (snd (fst xyzw))),
                                             SmartCast_base (Var (snd xyzw))))
       end.

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
  Definition SmartCast_op1 {var T1 T2} (opc : forall t, op (Tbase t) (Tbase t))
             (args1 : exprf base_type op (var:=var) (Tbase T1))
             (args2 : interp_flat_type Bounds.interp_base_type (Tbase T2))
    : exprf base_type op (var:=var) (Tbase T1)
    := SmartCast_base (Op (opc (bounds2_to_base_type (args2, interp_op (opc _) args2)))
                          (SmartCast_base args1)).
  Definition SmartCast_op2 {var T1 T2} (opc : forall t, op (Tbase t * Tbase t) (Tbase t))
             (args1 : exprf base_type op (var:=var) (Tbase T1 * Tbase T1))
             (args2 : interp_flat_type Bounds.interp_base_type (Tbase T2 * Tbase T2))
    : exprf base_type op (var:=var) (Tbase T1)
    := SmartCast_base (Op (opc (bounds3_to_base_type (args2) (interp_op (opc _) args2)))
                          (PairCast args1)).
  Definition SmartCast_op4 {var T1 T2} (opc : forall t, op (Tbase t * Tbase t * Tbase t * Tbase t) (Tbase t))
             (args1 : exprf base_type op (var:=var) (Tbase T1 * Tbase T1 * Tbase T1 * Tbase T1))
             (args2 : interp_flat_type Bounds.interp_base_type (Tbase T2 * Tbase T2 * Tbase T2 * Tbase T2))
    : exprf base_type op (var:=var) (Tbase T1)
    := SmartCast_base (Op (opc (bounds5_to_base_type (args2) (interp_op (opc _) args2)))
                          (QuadCast args1)).
  Definition cast_bound_op {var}
             {src1 dst1 src2 dst2}
             (opc1 : op src1 dst1)
             (opc2 : op src2 dst2)
    : forall (args1 : exprf base_type op (var:=var) src1)
             (args2 : interp_flat_type interp_base_type src2),
      exprf base_type op (var:=var) dst1
    := match opc1 in op src1 dst1, opc2 in op src2 dst2
             return (forall (args1 : exprf base_type op (var:=var) src1)
                            (args2 : interp_flat_type interp_base_type src2),
                        exprf base_type op (var:=var) dst1)
       with
       | OpConst _ _ as e, _ => fun _ _ => Op e TT
       | Add T1, Add T2 => SmartCast_op2 Add
       | Sub T1, Sub T2 => SmartCast_op2 Sub
       | Mul T1, Mul T2 => SmartCast_op2 Mul
       | Shl T1, Shl T2 => SmartCast_op2 Shl
       | Shr T1, Shr T2 => SmartCast_op2 Shr
       | Land T1, Land T2 => SmartCast_op2 Land
       | Lor T1, Lor T2 => SmartCast_op2 Lor
       | Neg T1 int_width1, Neg T2 int_width2
         => SmartCast_op1 (fun T => Neg T int_width1)
       | Cmovne T1, Cmovne T2 => SmartCast_op4 Cmovne
       | Cmovle T1, Cmovle T2 => SmartCast_op4 Cmovle
       | Cast A1 B1, Cast A2 B2 => fun args1 args2 => SmartCast_base args1
       | Add _ as e, _
       | Sub _ as e, _
       | Mul _ as e, _
       | Shl _ as e, _
       | Shr _ as e, _
       | Land _ as e, _
       | Lor _ as e, _
       | Neg _ _ as e, _
       | Cmovne _ as e, _
       | Cmovle _ as e, _
       | Cast _ _ as e, _
         => fun args1 _ => Op e args1
       end.
  Definition ZToBounds (z : Z) : bounds := {| lower := z ; upper := z |}.
  Definition of_Z (z : Z) : t := Some (ZToBounds z).

  Definition of_interp t (z : Syntax.interp_base_type t) : interp_base_type t
    := Some (ZToBounds (match t return Syntax.interp_base_type t -> Z with
                        | TZ => fun z => z
                        | TWord logsz => FixedWordSizes.wordToZ
                        end z)).
  Local Notation new_flat_type (*: forall t, interp_flat_type interp_base_type2 t -> flat_type base_type_code1*)
    := (@SmartFlatTypeMap2 _ _ interp_base_type (fun t v => Tbase (bounds_to_base_type v))).
  Lemma new_flat_type_Pair {A B} (v : interp_flat_type _ A * interp_flat_type _ B)
    : @new_flat_type (Prod A B) v = Prod (new_flat_type (fst v)) (new_flat_type (snd v)).
  Proof. reflexivity. Qed.
  Local Ltac rewrite_new_flat_type_Pair :=
    match goal with
    | [ |- context[@new_flat_type (Prod ?A ?B) ?VVV] ]
      => progress change (@new_flat_type (Prod A B) VVV) with (Prod (@new_flat_type A (fst VVV)) (@new_flat_type B (snd VVV))) in *
    | [ H : context[@new_flat_type (Prod ?A ?B) ?VVV] |- _ ]
      => progress change (@new_flat_type (Prod A B) VVV) with (Prod (@new_flat_type A (fst VVV)) (@new_flat_type B (snd VVV))) in *
    end.
  Definition new_type {t}
    : forall (ve : interp_flat_type interp_base_type (domain t))
             (v : interp_type interp_base_type t),
      type base_type
    := fun ve v => Arrow (@new_flat_type (domain t) ve) (@new_flat_type (codomain t) (v ve)).
  Definition SmartBoundv {var t} (bounds : interp_flat_type Bounds.interp_base_type t) (e : interp_flat_type var t)
    : interp_flat_type (fun t => @exprf base_type op var (Tbase t)) (new_flat_type bounds)
    := SmartFlatTypeMap2Interp2 (f:=fun _ _ => Tbase _) (fun t b v => SmartCast_base (Var v)) bounds e.
  Definition map_cast_const {t} (bounds : interp_flat_type Bounds.interp_base_type t) (e : interp_flat_type Syntax.interp_base_type t)
    : interp_flat_type Syntax.interp_base_type (new_flat_type bounds)
    := SmartFlatTypeMap2Interp2 (f:=fun _ _ => Tbase _) (fun t b v => cast_const v) bounds e.
  Definition map_uncast_const {t} (bounds : interp_flat_type Bounds.interp_base_type t) (e : interp_flat_type Syntax.interp_base_type (new_flat_type bounds))
    : interp_flat_type Syntax.interp_base_type t
    := SmartFlatTypeMapUnInterp2 (f:=fun _ _ => Tbase _) (fun t b v => cast_const v) e.
  Definition SmartUnboundv {var t} {bounds : interp_flat_type Bounds.interp_base_type t}
             (e : interp_flat_type var (new_flat_type bounds))
    : interp_flat_type (fun t => @exprf base_type op var (Tbase t)) t
    := SmartFlatTypeMapUnInterp2 (f:=fun _ _ => Tbase _) (fun t b (v : var _) => SmartCast_base (Var v)) e.
  Definition SmartBound {t} (e : Expr base_type op t)
             (input_bounds : interp_flat_type Bounds.interp_base_type (domain t))
    : Expr base_type op (new_type input_bounds (Interp (@Bounds.interp_op) e))
    := fun var => Abs (fun x => LetIn
                                  (LetIn (SmartPairf (SmartUnboundv x))
                                         (invert_Abs (e var)))
                                  (fun v => SmartPairf (SmartBoundv _ v))).

  Lemma map_cast_const_Pair {A B} bounds e
    : @map_cast_const (Prod A B) bounds e
      = (map_cast_const (fst bounds) (fst e), map_cast_const (snd bounds) (snd e)).
  Proof. reflexivity. Qed.

  Lemma map_uncast_const_Pair {A B} bounds e
    : @map_uncast_const (Prod A B) bounds e
      = (map_uncast_const (fst bounds) (fst e), map_uncast_const (snd bounds) (snd e)).
  Proof. reflexivity. Qed.

  Lemma SmartUnboundv_Pair {var A B} bounds e
    : @SmartUnboundv var (Prod A B) bounds e
      = (SmartUnboundv (fst e), SmartUnboundv (snd e)).
  Proof. reflexivity. Qed.

  Lemma SmartBoundv_Pair {var A B} (bounds : interp_flat_type _ _ * interp_flat_type _ _)
        (e : interp_flat_type _ _ * interp_flat_type _ _)
    : @SmartBoundv var (Prod A B) bounds e
      = (SmartBoundv (t:=A) (fst bounds) (fst e), SmartBoundv (t:=B) (snd bounds) (snd e)).
  Proof. reflexivity. Qed.

  Local Hint Resolve List.in_or_app.

  Lemma wff_SmartUnboundv {var1 var2} t input_bounds
        (x : interp_flat_type var1 (new_flat_type (t:=t) input_bounds))
        (x' : interp_flat_type var2 (new_flat_type input_bounds))
    : wff (flatten_binding_list x x')
          (SmartPairf (SmartUnboundv x))
          (SmartPairf (SmartUnboundv x')).
  Proof.
    induction t; simpl in *;
      try rewrite_new_flat_type_Pair;
      rewrite ?SmartUnboundv_Pair, ?SmartPairf_Pair;
      try constructor;
      try solve [ eapply wff_in_impl_Proper; eauto ].
    { unfold SmartPairf, SmartUnboundv, SmartCast_base; simpl;
        break_match.
      { let H := match goal with H : _ = _ |- _ => H end in
        case H; repeat constructor. }
      { repeat constructor. } }
  Qed.

  Local Hint Resolve @wff_SmartUnboundv.

  Lemma wff_SmartBoundv {var1 var2} G t f x1 x2
        (Hwf : wff (op:=op) G (SmartVarf x1) (SmartVarf x2))
    : wff (var1:=var1) (var2:=var2) G
          (SmartPairf (SmartBoundv f x1))
          (SmartPairf (SmartBoundv (t:=t) f x2)).
  Proof.
    induction t; simpl in *;
      destruct_head' prod;
      rewrite ?SmartVarf_Pair in Hwf;
      rewrite ?SmartBoundv_Pair; simpl in *;
        try setoid_rewrite SmartPairf_Pair;
        inversion_wf;
        destruct_head' and;
        try constructor; eauto.
    { unfold SmartPairf, SmartBoundv, SmartCast_base, SmartFlatTypeMap2, SmartVarf in *; simpl in *.
      break_match; repeat (trivial || constructor). }
  Qed.

  Local Hint Resolve wff_SmartBoundv.

  Local Hint Resolve wff_SmartVarf.

  Lemma Wf_SmartBound {t} e input_bounds
        (Hwf : Wf e)
    : Wf (@SmartBound t e input_bounds).
  Proof.
    intros var1 var2; specialize (Hwf var1 var2).
    unfold SmartBound.
    destruct Hwf; constructor; intros; simpl.
    repeat constructor; eauto using wff_in_impl_Proper.
  Qed.

  (** We can squash [a -> b -> c] into [a -> c] if [min a b c = min a
      c], i.e., if the narrowest type we pass through in the original
      case is the same as the narrowest type we pass through in the
      new case. *)
  Definition squash_cast {var} (a b c : base_type) : @exprf base_type op var (Tbase a) -> @exprf base_type op var (Tbase c)
    := if base_type_beq (base_type_min b (base_type_min a c)) (base_type_min a c)
       then SmartCast_base
       else fun x => Op (Cast b c) (Op (Cast a b) x).
  Fixpoint maybe_push_cast {var t} (v : @exprf base_type op var t) : option (@exprf base_type op var t)
    := match v in exprf _ _ t return option (exprf _ _ t) with
       | Var _ _ as v'
         => Some v'
       | Op t1 tR opc args
         => match opc in op src dst return exprf _ _ src -> option (exprf _ _ dst) with
            | Cast b c
              => fun args
                 => match @maybe_push_cast _ _ args with
                    | Some (Op _ _ opc' args')
                      => match opc' in op src' dst' return exprf _ _ src' -> option (exprf _ _ (Tbase c)) with
                         | Cast a b
                           => fun args''
                              => Some (squash_cast a b c args'')
                         | OpConst _ v
                           => fun args''
                              => Some (SmartCast_base (Op (OpConst v) TT))
                         | _ => fun _ => None
                         end args'
                    | Some (Var _ v as v') => Some (SmartCast_base v')
                    | Some _ => None
                    | None => None
                    end
            | OpConst _ v
              => fun _ => Some (Op (OpConst v) TT)
            | _ => fun _ => None
            end args
       | Pair _ _ _ _
       | LetIn _ _ _ _
       | TT
         => None
       end.
  Definition push_cast {var t} : @exprf base_type op var t -> inline_directive (op:=op) (var:=var) t
    := match t with
       | Tbase _ => fun v => match maybe_push_cast v with
                             | Some e => inline e
                             | None => default_inline v
                             end
       | _ => default_inline
       end.

  Definition MapBounds {t}
             (e : Expr base_type op t)
             (input_bounds : interp_flat_type Bounds.interp_base_type (domain t))
    : Expr base_type op _
    := ExprEta
         (InlineConstGen
            (@push_cast)
            (Linearize
               (SmartBound
                  (@MapInterpCast
                     base_type Bounds.interp_base_type
                     op (@Bounds.interp_op)
                     (fun _ t => Op (OpConst (ZToInterp 0)) TT)
                     (@cast_bound_op)
                     t e input_bounds)
                  input_bounds))).

  Definition ComputeBounds {t} (e : Expr base_type op t)
             (input_bounds : interp_flat_type interp_base_type (domain t))
    : interp_flat_type interp_base_type (codomain t)
    := Interp (@interp_op) e input_bounds.

  (*Definition mapf_interpToZ_T (T : flat_type base_type) : flat_type base_type
    :=
*)
  Definition mapf_interpToZ {T} : interp_flat_type Syntax.interp_base_type T -> interp_flat_type (fun _ => Z) T
    := SmartVarfMap (fun _ => interpToZ).
  Definition mapf_interp_new_flat_typeToZ {T v} : interp_flat_type Syntax.interp_base_type (@new_flat_type T v) -> interp_flat_type (fun _ => Z) T
    := SmartFlatTypeMapUnInterp2 (f:=fun _ _ => Tbase _) (fun _ _ => interpToZ).
  Definition is_bounded_byb {T} : Syntax.interp_base_type T -> interp_base_type T -> bool
    := fun val bound
       => match bound with
          | Some bounds'
            => ((0 <=? lower bounds') && (lower bounds' <=? interpToZ val) && (interpToZ val <=? upper bounds'))
                 && (match bit_width_of_base_type T with
                     | Some sz => Z.log2 (upper bounds') <? sz
                     | None => true
                     end)
          | None => true
          end%bool%Z.
  Definition is_bounded_by' {T} : Syntax.interp_base_type T -> interp_base_type T -> Prop
    := fun val bound => is_bounded_byb val bound = true.

  Definition is_bounded_by {T} : interp_flat_type Syntax.interp_base_type T -> interp_flat_type interp_base_type T -> Prop
    := interp_flat_type_rel_pointwise (@is_bounded_by').
  (** XXX TODO: REMOVE ME (the global arguments directive) *)
  Global Arguments interp_flat_type_relb_pointwise {_ _ _} R {t} _ _.
  Definition is_bounded_by_bool {T} : interp_flat_type Syntax.interp_base_type T -> interp_flat_type interp_base_type T -> bool
    := interp_flat_type_relb_pointwise (@is_bounded_byb).

  Lemma mapf_interpToZ_Pair {A B} x
    : @mapf_interpToZ (Prod A B) x = (mapf_interpToZ (fst x), mapf_interpToZ (snd x)).
  Proof. reflexivity. Qed.
  Lemma mapf_interp_new_flat_typeToZ_Pair {A B} v e
    : @mapf_interp_new_flat_typeToZ (Prod A B) v e = (mapf_interp_new_flat_typeToZ (fst e), mapf_interp_new_flat_typeToZ (snd e)).
  Proof. reflexivity. Qed.

  (** TODO: move me *)
  Lemma cast_const_id {t} v
    : @cast_const t t v = v.
  Proof.
    destruct t; simpl; trivial.
    rewrite ZToWord_wordToZ; reflexivity.
  Qed.

  Lemma cast_const_idempotent {a b c} v
    : base_type_min b (base_type_min a c) = base_type_min a c
      -> @cast_const b c (@cast_const a b v) = @cast_const a c v.
  Proof.
    destruct a, b, c; simpl; try reflexivity; try congruence;
      intro H; inversion H; clear H;
        repeat match goal with
               | [ H : context[?min ?x ?y] |- _ ]
                 => revert H; apply (Min.min_case_strong x y); intros ? H; subst
               end;
        try rewrite ZToWord_wordToZ_ZToWord by omega *;
        try rewrite wordToZ_ZToWord_wordToZ by omega *;
        try reflexivity.
  Qed.

  Lemma interpf_maybe_push_cast t (e1 e2 : exprf base_type op t)
        (H : maybe_push_cast e1 = Some e2)
    : interpf Syntax.interp_op e1 = interpf Syntax.interp_op e2.
  Proof.
    revert dependent e2; induction e1; intro e2;
      try (preinvert_one_type e2; intros ? e2); destruct e2;
        try exact I;
        repeat match goal with
               | _ => intro
               | _ => reflexivity
               | [ H : forall e, Some _ = Some e -> _ |- _ ] => specialize (H _ eq_refl)
               | [ H : base_type_beq _ _ = true |- _ ] => apply internal_base_type_dec_bl in H
               | _ => progress subst
               | _ => progress inversion_option
               | _ => progress inversion_sigma
               | _ => progress inversion_prod
               | _ => progress inversion_expr
               | _ => progress simpl in *
               | _ => congruence
               | _ => progress break_match_hyps
               | _ => progress break_innermost_match_step
               | _ => progress invert_match_op
               | _ => progress invert_match_expr
               | _ => progress unfold SmartCast_base, squash_cast in *
               | _ => rewrite_hyp !*
               | _ => rewrite cast_const_id in *
               | _ => rewrite cast_const_idempotent by assumption
               end.
  Qed.

  Lemma interpf_push_cast t (e : exprf base_type op t)
    : interpf Syntax.interp_op (exprf_of_inline_directive (push_cast e)) = interpf Syntax.interp_op e.
  Proof.
    unfold push_cast;
      break_match; try reflexivity; simpl; [].
    symmetry; apply (@interpf_maybe_push_cast (Tbase _)); assumption.
  Qed.

  Local Hint Resolve interpf_push_cast.

  Local Hint Constructors wff.

  Local Ltac t_pair :=
    repeat first [ exact I
                 | intro
                 | progress subst
                 | progress destruct_head' False
                 | progress destruct_head' sig
                 | progress destruct_head' and
                 | progress inversion_option
                 | progress inversion_sigma
                 | progress inversion_prod
                 | progress break_match
                 | progress simpl in *
                 | progress inversion_wf ].

  Lemma wff_SmartCast_base {var1 var2} G A A' e1 e2
        (Hwf : wff G e1 e2)
    : wff G (@SmartCast_base var1 A A' e1) (@SmartCast_base var2 A A' e2).
  Proof.
    unfold SmartCast_base; break_match; auto.
  Qed.

  Local Hint Resolve @wff_SmartCast_base.

  Local Hint Extern 2 => progress simpl.

  Lemma wff_PairCast {var1 var2} G a b a' b'
        (e1 e2 : exprf base_type op (Tbase a * Tbase b))
        (Hwf : wff (var1:=var1) (var2:=var2) G e1 e2)
    : wff (t:=Prod (Tbase a') (Tbase b')) G (PairCast e1) (PairCast e2).
  Proof.
    apply wff_encode in Hwf; unfold wff_code in *;
      preinvert_one_type e1; intros ? e1; destruct e1; try exact I; t_pair;
        preinvert_one_type e2; intros ? e2; destruct e2; try exact I; t_pair;
          repeat constructor; eauto 6.
  Qed.

  Local Hint Resolve wff_PairCast.

  Lemma wff_QuadCast {var1 var2} G a b c d a' b' c' d'
        (e1 e2 : exprf base_type op (Tbase a * Tbase b * Tbase c * Tbase d))
        (Hwf : wff (var1:=var1) (var2:=var2) G e1 e2)
    : wff G (@QuadCast var1 a b c d a' b' c' d' e1) (QuadCast e2).
  Proof.
    apply wff_encode in Hwf; unfold wff_code in *;
      repeat match goal with
             | [ e : exprf _ _ (_ * _) |- _ ]
               => preinvert_one_type e; intros ? e; destruct e; try exact I; t_pair
             end;
      repeat constructor; eauto 10.
  Qed.

  Local Hint Resolve wff_QuadCast.

  Lemma wff_cast_bound_op {ovar1 ovar2} G src1 dst1 src2 dst2
        (opc1 : op src1 dst1) (opc2 : op src2 dst2)
        (e1 e2 : exprf base_type op src1)
        (args2 : interp_flat_type interp_base_type src2)
        (Hwf : wff (var1:=ovar1) (var2:=ovar2) G e1 e2)
    : wff G (cast_bound_op opc1 opc2 e1 args2) (cast_bound_op opc1 opc2 e2 args2).
  Proof.
    destruct opc1, opc2; simpl; auto;
      unfold SmartCast_op1, SmartCast_op2, SmartCast_op4, SmartCast_base; break_match; subst;
        trivial;
        try constructor; trivial; eauto.
  Qed.

  Local Hint Resolve wff_cast_bound_op : wf.

  Local Hint Resolve Wf_Linearize Wf_SmartBound Wf_MapInterpCast : wf.

  Lemma interpf_SmartCast_base {A A'} e
    : interpf (@Syntax.interp_op) (@SmartCast_base _ A A' e) = cast_const (interpf (@Syntax.interp_op) e).
  Proof.
    unfold SmartCast_base; break_match; rewrite ?cast_const_id; reflexivity.
  Qed.

  Lemma interpf_PairCast {A B A' B'} e
    : interpf (@Syntax.interp_op) (@PairCast _ A B A' B' e)
      = let ev := interpf (@Syntax.interp_op) e in
        (cast_const (fst ev), cast_const (snd ev)).
  Proof.
    invert_expr; break_innermost_match; try exact I; simpl;
      cbv [LetIn.Let_In];
      rewrite ?interpf_SmartCast_base;
      reflexivity.
  Qed.

  Lemma interpf_QuadCast {A B C D A' B' C' D'} e
    : interpf (@Syntax.interp_op) (@QuadCast _ A B C D A' B' C' D' e)
      = let ev := interpf (@Syntax.interp_op) e in
        (cast_const (fst (fst (fst ev))),
         cast_const (snd (fst (fst ev))),
         cast_const (snd (fst ev)),
         cast_const (snd ev)).
  Proof.
    repeat first [ exact I
                 | reflexivity
                 | rewrite !interpf_SmartCast_base
                 | progress cbv [LetIn.Let_In]
                 | progress simpl
                 | progress break_innermost_match
                 | progress invert_expr ].
  Qed.

  Lemma interpf_PairCast_uniform {A A'} e
    : interpf (@Syntax.interp_op) (@PairCast _ A A A' A' e)
      = SmartVarfMap (fun t => cast_const) (interpf (@Syntax.interp_op) e).
  Proof. rewrite interpf_PairCast; reflexivity. Qed.

  Lemma interpf_QuadCast_uniform {A A'} e
    : interpf (@Syntax.interp_op) (@QuadCast _ A A A A A' A' A' A' e)
      = SmartVarfMap (fun t => cast_const) (interpf (@Syntax.interp_op) e).
  Proof. rewrite interpf_QuadCast; reflexivity. Qed.

  Local Ltac rewrite_in_all lem :=
    match goal with
    | _ => rewrite lem
    | [ H : _ |- _ ] => rewrite lem in H
    end.

  Local Ltac t_interpf_step :=
    first [ reflexivity
          | assumption
          | progress destruct_head_hnf' unit
          | progress destruct_head_hnf' and
          | progress rewrite_new_flat_type_Pair
          | rewrite_in_all SmartBoundv_Pair
          | rewrite_in_all SmartUnboundv_Pair
          | rewrite_in_all SmartPairf_Pair
          | rewrite_in_all interpf_SmartCast_base
          | rewrite_in_all map_cast_const_Pair
          | rewrite_in_all map_uncast_const_Pair
          | rewrite_in_all mapf_interpToZ_Pair
          | rewrite_in_all mapf_interp_new_flat_typeToZ_Pair
          | rewrite Z2Nat.id by auto with zarith
          | progress split_andb
          | rewrite_hyp !*
          | progress (simpl @fst; simpl @snd)
          | progress break_match_hyp
          | progress subst
          | progress break_innermost_match_step
          | progress Z.ltb_to_lt
          | rewrite_in_all Z.pow_Zpow
          | omega ].

  Lemma interpf_SmartPairf_SmartBoundv {t} bounds e
    : interpf (@Syntax.interp_op) (SmartPairf (@SmartBoundv (@Syntax.interp_base_type) t bounds e))
      = map_cast_const bounds e.
  Proof.
    induction t;
      repeat first [ t_interpf_step
                   | progress simpl in *
                   | progress unfold SmartPairf, SmartBoundv, SmartFlatTypeMap2 ].
  Qed.

  Lemma interpf_SmartPairf_SmartUnboundv {t} bounds e
    : interpf (@Syntax.interp_op) (SmartPairf (@SmartUnboundv (@Syntax.interp_base_type) t bounds e))
      = map_uncast_const bounds e.
  Proof.
    induction t;
      repeat first [ t_interpf_step
                   | progress simpl in *
                   | progress unfold SmartPairf, SmartUnboundv, SmartFlatTypeMap2 ].
  Qed.

  Local Arguments Z.add !_ !_.
  Local Existing Instances Z.add_le_Proper Z.sub_le_eq_Proper Z.log2_up_le_Proper Z.pow_Zpos_le_Proper.
  Lemma mapf_interp_new_flat_typeToZ__map_cast_const {t} bounds e
        (Hbounded : is_bounded_by e bounds)
    : mapf_interp_new_flat_typeToZ (@map_cast_const t bounds e)
      = mapf_interpToZ e.
  Proof.
    induction t;
      repeat first [ t_interpf_step
                   | progress simpl in *
                   | progress unfold map_cast_const, mapf_interp_new_flat_typeToZ
                   | progress unfold is_bounded_by in *
                   | progress unfold mapf_interpToZ, SmartVarfMap in *
                   | progress unfold cast_const, bounds_to_base_type'
                   | rewrite wordToZ_ZToWord
                   | split; [ reflexivity | ]
                   | match goal with
                     | [ |- (?x < ?y)%Z ]
                       => cut (x <= y - 1)%Z; [ omega | ]
                     end
                   | rewrite <- !Z.log2_up_le_full
                   | progress unfold is_bounded_by', is_bounded_byb in * ].
  Qed.

  Section bounded_by_interp_op.
    Local Notation is_bounded_by_interp_opT opc
      := (forall t sv1 sv2,
             is_bounded_by sv1 sv2
             -> is_bounded_by (Syntax.interp_op _ _ (opc t) sv1) (interp_op (opc t) sv2))
           (only parsing).

    Local Ltac fin_t :=
      first [ reflexivity
            | omega
            | match goal with |- context[(_ * _)%Z] => idtac end;
              nia ].

    Local Ltac intro_t :=
      first [ progress simpl in *
            | progress intros ].

    Local Ltac break1_t :=
      first [ progress subst
            | progress destruct_head_hnf' unit
            | progress inversion_bounds
            | progress inversion_option
            | progress destruct_head' and
            | progress destruct_head' prod
            | progress destruct_head_hnf' bounds
            | progress split_andb
            | progress split_and ].
    Local Ltac break2_t :=
      first [ progress destruct_head' base_type
            | progress destruct_head_hnf' option
            | progress destruct_head' or
            | progress break_innermost_match_step ].
    Local Ltac unfolder_t :=
      first [ progress unfold is_bounded_by', is_bounded_byb in *
            | progress unfold SmartBuildBounds, SmartVarfMap in *
            | progress unfold neg, cmovle, cmovne in *
            | progress unfold ModularBaseSystemListZOperations.wneg, ModularBaseSystemListZOperations.neg, ModularBaseSystemListZOperations.wcmovne, ModularBaseSystemListZOperations.cmovne, ModularBaseSystemListZOperations.wcmovl, ModularBaseSystemListZOperations.cmovl in * ].
    Local Ltac late_unfolder_t :=
      first [ progress unfold wneg_gen, wcmovl_gen, wcmovne_gen in * ].

    (* split the goal, but only if it's about Z, not word *)
    Local Ltac Z_andb_splitter_t :=
      lazymatch goal with
      | [ sz : nat |- _ ] => fail
      | [ w : FixedWordSizes.wordT _ |- _ ] => fail
      | [ w : word _ |- _ ] => fail
      | [ |- andb _ _ = true ] => apply Bool.andb_true_iff, conj
      end.

    Local Ltac rewriter1_t :=
      match goal with
      | [ H : true = true |- _ ] => clear H
      | [ H : ?x = true, H' : context[?x] |- _ ] => rewrite H in H'
      | [ H : ?x = true |- context[?x] ] => rewrite H
      | _ => rewrite Bool.andb_true_r
      | _ => rewrite Bool.andb_true_l
      | [ H : andb _ _ = false |- _ ] => apply Bool.andb_false_iff in H
      | _ => rewrite wordToZ_gen_ZToWord_gen
          by eauto using Z.ones_nonneg, (fun a b pf => proj2 (Z.log2_lt_pow2_alt a b pf)), Z.le_lt_trans, Z.log2_nonneg with omega
      | _ => rewrite wordToZ_ZToWord
          by eauto using Z.ones_nonneg, (fun a b pf => proj2 (Z.log2_lt_pow2_alt a b pf)), Z.le_lt_trans, Z.log2_nonneg with omega
      end.

    Local Ltac Zltb_to_lt :=
      first [ progress Z.ltb_to_lt
            | match goal with
              | [ |- ((_ <=? _) && (_ <=? _))%Z%bool = true ]
                => rewrite Bool.andb_true_iff, !Z.leb_le
              end ].

    Local Ltac simpler_t :=
      first [ progress specialize_by auto
            | match goal with
              | [ H : context[Z.of_N (wordToN ?x)] |- _ ]
                => change (Z.of_N (wordToN x)) with (FixedWordSizes.wordToZ_gen x) in *
              | [ |- context[Z.of_N (wordToN ?x)] ]
                => change (Z.of_N (wordToN x)) with (FixedWordSizes.wordToZ_gen x) in *
              | [ H : (?x <= ?x)%Z |- _ ] => clear H
              | [ H : FixedWordSizes.wordToZ ?x = _ |- _ ]
                => generalize dependent (FixedWordSizes.wordToZ x); clear x; intros; subst
              | [ H : _ = FixedWordSizes.wordToZ ?x |- _ ]
                => generalize dependent (FixedWordSizes.wordToZ x); clear x; intros; subst
              end ].

    Local Ltac misc_solver_t :=
      solve [ eauto using Z.shiftl_le_mono, Z.shiftr_le_mono, Z.ones_nonneg with nocore omega
            | apply Z.land_nonneg; eauto with nocore omega
            | apply Z.min_case_strong;
              eauto using Z.land_upper_bound_r, Z.land_upper_bound_l, Z.le_trans with nocore omega
            | apply Z.lor_bounds_gen_lower; eauto using Z.max_le_compat with omega
            | autorewrite with push_Zmax;
              apply Z.lor_bounds_gen_upper; eauto using Z.le_max_l, Z.le_max_r, Z.le_trans with omega
            | apply Z.max_case_strong; omega ].

    Local Ltac t_step :=
      first [ fin_t
            | intro_t
            | break1_t
            | unfolder_t
            | rewriter1_t
            | simpler_t
            | Z_andb_splitter_t
            | break2_t
            | Zltb_to_lt
            | progress adjust_mbs_wops
            | misc_solver_t
            | progress syntactic_fixed_size_op_to_word
            | late_unfolder_t ].
    Local Ltac t := repeat t_step.

    Local Ltac cutZ :=
      let G := match goal with |- forall t, @?G t => G end in
      let t := fresh in
      intro t;
      cut (G TZ);
      [ destruct t; [ solve [ trivial ]
                    | let H := fresh in
                      let b := fresh in
                      let v := fresh in
                      intros H v b;
                      specialize (H (SmartVarfMap (fun _ => interpToZ) v) b) ]
      | clear t ].

    Lemma add_is_bounded_by_interp_op : is_bounded_by_interp_opT Add.
    Proof. cutZ; t. split; eapply wadd_valid_update; eauto. Qed.
    Local Hint Resolve add_is_bounded_by_interp_op.
    Lemma sub_is_bounded_by_interp_op : is_bounded_by_interp_opT Sub.
    Proof. cutZ; t. split; eapply wsub_valid_update; eauto. Qed.
    Local Hint Resolve sub_is_bounded_by_interp_op.
    Lemma mul_is_bounded_by_interp_op : is_bounded_by_interp_opT Mul.
    Proof. cutZ; t. split; eapply wmul_valid_update; eauto. Qed.
    Local Hint Resolve mul_is_bounded_by_interp_op.
    Lemma shl_is_bounded_by_interp_op : is_bounded_by_interp_opT Shl.
    Proof. cutZ; t. split; eapply wshl_valid_update; eauto. Qed.
    Local Hint Resolve shl_is_bounded_by_interp_op.
    Lemma shr_is_bounded_by_interp_op : is_bounded_by_interp_opT Shr.
    Proof. cutZ; t. split; eapply wshr_valid_update; eauto. Qed.
    Local Hint Resolve shr_is_bounded_by_interp_op.
    Lemma land_is_bounded_by_interp_op : is_bounded_by_interp_opT Land.
    Proof. cutZ; t. split; eapply wland_valid_update; eauto with omega. Qed.
    Local Hint Resolve land_is_bounded_by_interp_op.
    Lemma lor_is_bounded_by_interp_op : is_bounded_by_interp_opT Lor.
    Proof. cutZ; t. split; eapply wlor_valid_update; eauto. Qed.
    Local Hint Resolve lor_is_bounded_by_interp_op.
    Lemma neg_is_bounded_by_interp_op int_size : is_bounded_by_interp_opT (fun T => Neg T int_size).
    Proof. cutZ; t. Qed.
    Local Hint Resolve neg_is_bounded_by_interp_op.
    Lemma cmovne_is_bounded_by_interp_op : is_bounded_by_interp_opT Cmovne.
    Proof. cutZ; t. Qed.
    Local Hint Resolve cmovne_is_bounded_by_interp_op.
    Lemma cmovle_is_bounded_by_interp_op : is_bounded_by_interp_opT Cmovle.
    Proof. cutZ; t. Qed.
    Local Hint Resolve cmovle_is_bounded_by_interp_op.
    Lemma cast_is_bounded_by_interp_op T : is_bounded_by_interp_opT (Cast T).
    Proof. t. Qed.
    Local Hint Resolve cast_is_bounded_by_interp_op.

    Lemma is_bounded_by_interp_op src dst (op : op src dst)
      : forall (sv1 : interp_flat_type Syntax.interp_base_type src)
               (sv2 : interp_flat_type interp_base_type src)
               (H : is_bounded_by sv1 sv2),
        is_bounded_by (Syntax.interp_op src dst op sv1) (interp_op op sv2).
    Proof.
      destruct op; auto.
      { (* const casse *) t. }
    Qed.
  End bounded_by_interp_op.

  Lemma InterpSmartBound t e input_bounds
        (Hwf : Wf e)
    : forall (x : interp_flat_type Syntax.interp_base_type (new_flat_type (t:=domain t) input_bounds)),
      is_bounded_by (map_uncast_const input_bounds x) input_bounds
      -> mapf_interp_new_flat_typeToZ (Interp (@Syntax.interp_op) (SmartBound e input_bounds) x)
         = mapf_interpToZ (Interp (@Syntax.interp_op) e (map_uncast_const input_bounds x)).
  Proof.
    unfold SmartBound, Interp; simpl.
    cbv [LetIn.Let_In]; intros x H.
    rewrite interpf_SmartPairf_SmartBoundv, interpf_SmartPairf_SmartUnboundv, interpf_invert_Abs, mapf_interp_new_flat_typeToZ__map_cast_const; [ reflexivity | ].
    fold (@Interp _ _ _ (@interp_op) _ e).
    fold (@Interp _ _ _ (@Syntax.interp_op) _ e).
    apply InterpWf; [ | assumption.. ].
    intros src dst op sv1 sv2.
    fold (is_bounded_by sv1 sv2).
    fold (is_bounded_by (Syntax.interp_op src dst op sv1) (interp_op op sv2)).
    apply is_bounded_by_interp_op.
  Qed.

  Lemma interpf_SmartCast_op1 {T1 T2} (opc : forall t, op (Tbase t) (Tbase t)) args1 args2
        (HopcZ : forall T2 x xb zb,
            is_bounded_by (T:=Tbase TZ) x (Some xb)
            -> interp_op (opc T2) (Some xb) = Some zb
            -> FixedWordSizes.wordToZ (Syntax.interp_op _ _ (opc (TWord (Z.to_nat (Z.log2_up (Z.log2_up (Z.max (1 + upper xb) (1 + upper zb))))))) (FixedWordSizes.ZToWord x))
               = Syntax.interp_op _ _ (opc TZ) x)
        (Hb : is_bounded_by (interpf (@Syntax.interp_op) args1) args2)
    : interpf (@Syntax.interp_op) (@SmartCast_op1 _ T1 T2 opc args1 args2)
      = cast_const (Syntax.interp_op _ _ (opc TZ) (SmartVarfMap (fun t => @cast_const t TZ) (interpf (@Syntax.interp_op) args1))).
  Proof.
    unfold SmartCast_op1.
    unfold is_bounded_by, interp_flat_type_rel_pointwise, interp_flat_type_rel_pointwise_gen_Prop, is_bounded_by', is_bounded_byb in *.
    rewrite interpf_SmartCast_base; simpl.
    repeat unfold bounds3_to_base_type, bounds2_to_base_type, bounds_to_base_type, bounds_to_base_type', cast_const, ZToInterp, interpToZ; simpl.
    unfold base_type_max.
    unfold SmartVarfMap; simpl.
    unfold bit_width_of_base_type in *.
    rewrite interpf_SmartCast_base.
    repeat (break_innermost_match_step; simpl; try reflexivity);
      destruct_head' and;
      split_andb;
      generalize dependent (interpf Syntax.interp_op args1); clear args1; intros;
        simpl in *;
        rewrite <- !Z2Nat.inj_max, !Z.max_log2_up;
        erewrite HopcZ by (rewrite_hyp !*; reflexivity);
        reflexivity.
  Qed.

  Lemma interpf_SmartCast_op2 {T1 T2} (opc : forall t, op (Tbase t * Tbase t) (Tbase t)) args1 args2
        (HopcZ : forall T2 x y xb yb zb,
            is_bounded_by (T:=Prod (Tbase TZ) (Tbase TZ)) (x, y)%core (Some xb, Some yb)%core
            -> interp_op (opc T2) (Some xb, Some yb) = Some zb
            -> FixedWordSizes.wordToZ (Syntax.interp_op _ _ (opc (TWord (Z.to_nat (Z.log2_up (Z.log2_up (Z.max (Z.max (1 + upper xb) (1 + upper yb)) (1 + upper zb))))))) (FixedWordSizes.ZToWord x, FixedWordSizes.ZToWord y))
               = Syntax.interp_op _ _ (opc TZ) (x, y))
        (Hb : is_bounded_by (interpf (@Syntax.interp_op) args1) args2)
    : interpf (@Syntax.interp_op) (@SmartCast_op2 _ T1 T2 opc args1 args2)
      = cast_const (Syntax.interp_op _ _ (opc TZ) (SmartVarfMap (fun t => @cast_const t TZ) (interpf (@Syntax.interp_op) args1))).
  Proof.
    unfold SmartCast_op2.
    unfold is_bounded_by, interp_flat_type_rel_pointwise, interp_flat_type_rel_pointwise_gen_Prop, is_bounded_by', is_bounded_byb in *.
    rewrite interpf_SmartCast_base; simpl.
    rewrite interpf_PairCast_uniform.
    destruct_head_hnf prod.
    repeat unfold bounds3_to_base_type, bounds2_to_base_type, bounds_to_base_type, bounds_to_base_type', cast_const, ZToInterp, interpToZ; simpl.
    unfold base_type_max.
    unfold SmartVarfMap; simpl.
    unfold bit_width_of_base_type in *.
    repeat (break_innermost_match_step; simpl; try reflexivity);
      destruct_head' and;
      split_andb;
      generalize dependent (interpf Syntax.interp_op args1); clear args1; intros; destruct_head_hnf prod;
        rewrite <- !Z2Nat.inj_max, !Z.max_log2_up;
        erewrite HopcZ by (eassumption || rewrite_hyp !*; auto);
        reflexivity.
  Qed.

  Lemma interpf_SmartCast_op4 {T1 T2} (opc : forall t, op (Tbase t * Tbase t * Tbase t * Tbase t) (Tbase t)) args1 args2
        (HopcZ : forall T2 x y z w xb yb zb wb ob,
            is_bounded_by (T:=Prod (Prod (Prod (Tbase TZ) (Tbase TZ)) (Tbase TZ)) (Tbase TZ))
                          (x, y, z, w)%core (Some xb, Some yb, Some zb, Some wb)%core
            -> interp_op (opc T2) (Some xb, Some yb, Some zb, Some wb) = Some ob
            -> FixedWordSizes.wordToZ (Syntax.interp_op _ _ (opc (TWord (Z.to_nat (Z.log2_up (Z.log2_up (Z.max (Z.max (Z.max (1 + upper xb) (1 + upper yb)) (Z.max (1 + upper zb) (1 + upper wb))) (1 + upper ob)))))))
                                                        (FixedWordSizes.ZToWord x, FixedWordSizes.ZToWord y, FixedWordSizes.ZToWord z, FixedWordSizes.ZToWord w))
               = Syntax.interp_op _ _ (opc TZ) (x, y, z, w))
        (Hb : is_bounded_by (interpf (@Syntax.interp_op) args1) args2)
    : interpf (@Syntax.interp_op) (@SmartCast_op4 _ T1 T2 opc args1 args2)
      = cast_const (Syntax.interp_op _ _ (opc TZ) (SmartVarfMap (fun t => @cast_const t TZ) (interpf (@Syntax.interp_op) args1))).
  Proof.
    unfold SmartCast_op4.
    unfold is_bounded_by, interp_flat_type_rel_pointwise, interp_flat_type_rel_pointwise_gen_Prop, is_bounded_by', is_bounded_byb in *.
    rewrite interpf_SmartCast_base; simpl.
    rewrite interpf_QuadCast_uniform.
    destruct_head_hnf prod.
    repeat unfold bounds5_to_base_type, bounds4_to_base_type, bounds3_to_base_type, bounds2_to_base_type, bounds_to_base_type, bounds_to_base_type', cast_const, ZToInterp, interpToZ; simpl.
    unfold base_type_max.
    unfold SmartVarfMap; simpl.
    unfold bit_width_of_base_type in *.
    repeat (break_innermost_match_step; simpl; try reflexivity);
      destruct_head' and;
      split_andb;
      generalize dependent (interpf Syntax.interp_op args1); clear args1; intros; destruct_head_hnf prod;
        rewrite <- !Z2Nat.inj_max, !Z.max_log2_up;
        erewrite HopcZ by (eassumption || rewrite_hyp !*; auto);
        reflexivity.
  Qed.

  Definition bound_is_goodb : forall t, interp_base_type t -> bool
    := fun t bs
       => match bs with
          | Some bs
            => (*let l := lower bs in
               let u := upper bs in
               let bit_width := bit_width_of_base_type t in
               ((0 <=? l) && (match bit_width with Some bit_width => Z.log2 u <? bit_width | None => true end))%Z%bool*)
            true
          | None => false
          end.
  Definition bound_is_good : forall t, interp_base_type t -> Prop
    := fun t v => bound_is_goodb t v = true.
  Local Notation bounds_are_good
    := (@interp_flat_type_rel_pointwise1 _ _ bound_is_good).

    Lemma interpf_cast_bound_op G t0 tR (opc : op t0 tR)
        (ein eout ebounds : exprf base_type op t0)
        (HG : forall (t : base_type) (x : Syntax.interp_base_type t) (x' : interp_base_type t),
            List.In (existT _ t (x, x')) G
            -> is_bounded_by' x x')
        (Hwf : wff G ein ebounds)
        (He : interpf Syntax.interp_op ein = interpf Syntax.interp_op eout)
        (Hbounds_are_good : bounds_are_good (interpf (@interp_op) (Op opc ebounds)))
    : interpf Syntax.interp_op (cast_bound_op opc opc eout (interpf (@interp_op) ebounds))
      = interpf Syntax.interp_op (Op opc ein).
  Proof.
    assert (Hb : is_bounded_by (interpf Syntax.interp_op (Op opc ein)) (interpf (@interp_op) (Op opc ebounds)))
      by (eapply interpf_wff; eauto; apply is_bounded_by_interp_op).
    assert (Hb0 : is_bounded_by (interpf Syntax.interp_op ein) (interpf (@interp_op) ebounds))
      by (eapply interpf_wff; eauto; apply is_bounded_by_interp_op).
    destruct opc;
      repeat first [ intro
                   | reflexivity
                   | progress subst
                   | progress destruct_head' and
                   | solve [ rewrite_hyp <- ?*; eapply interpf_wff; [ .. | eassumption ]; eauto;
                             apply is_bounded_by_interp_op
                           | inversion_wf; eauto ]
                   | rewrite interpf_SmartCast_base
                   | rewrite interpf_SmartCast_op1
                   | rewrite interpf_SmartCast_op2
                   | rewrite interpf_SmartCast_op4
                   | rewrite_hyp !*
                   | progress simpl in *
                   | progress break_innermost_match ].
    all:unfold is_bounded_by', is_bounded_byb in *.
    all:simpl in *.
    { repeat first [ progress unfold add, add' in *
                   | progress unfold t_map2, SmartBuildBounds, bound_is_good, bound_is_goodb in *
                   | progress subst
                   | progress inversion_option
                   | progress split_andb
                   | progress break_match_hyps
                   | progress Z.ltb_to_lt
                   | progress simpl in *
                   | progress rewrite_hyp <- ?*
                   | match goal with
                     | [ H : context[andb _ _ = false] |- _ ] => rewrite Bool.andb_false_iff in H
                     end
                   | progress destruct_head' or
                   | exfalso; omega
                   | congruence ].
      { Local Ltac def_ZToWord_t :=
          first [ eapply Z.le_lt_trans; [ apply Z.log2_le_mono | eassumption ]; omega ].
        rewrite wadd_def_ZToWord by def_ZToWord_t.
        reflexivity. } }
    { repeat first [ progress unfold add, add' in *
                   | progress unfold t_map2, SmartBuildBounds, bound_is_good, bound_is_goodb, bit_width_of_base_type in *
                   | progress subst
                   | progress inversion_option
                   | progress split_andb
                   | progress break_match_hyps
                   | progress Z.ltb_to_lt
                   | progress simpl in *
                   | progress rewrite_hyp <- ?*
                   | match goal with
                     | [ H : context[andb _ _ = false] |- _ ] => rewrite Bool.andb_false_iff in H
                     end
                   | progress destruct_head' or
                   | exfalso; omega
                   | congruence ].
      { rewrite wadd_def_ZToWord;
          repeat rewrite !wordToZ_ZToWord.
        reflexivity.
        all:try split; try omega.
        all:rewrite ?Z.pow_Zpow, ?Z2Nat.id, ?Nat2Z.inj_succ, ?Nat2Z.inj_0, <- ?Z.one_succ, <- ?Z.two_succ.
        all:auto using Z.log2_up_nonneg.
        all: repeat apply Z.max_case_strong; intros.
        all: try (eapply Z.lt_le_trans; [ | rewrite <- !Z.log2_up_le_full_max; reflexivity ]).
        all: repeat apply Z.max_case_strong; intros.
        all: try (eapply Z.lt_le_trans; [ | rewrite <- !Z.log2_up_le_full_max; reflexivity ]).
        all: repeat apply Z.max_case_strong; intros.
        all: try omega.
        all: change (2^1)%Z with 2%Z in *.
        all: try omega.
        all:repeat match goal with
                   | [ H : (Z.log2_up _ <= 1)%Z |- _ ] => apply Z.log2_up_le_1 in H
                   | [ H : (1 <= Z.log2_up _)%Z |- _ ] => apply Z.log2_up_1_le in H
                   end.
        all: try omega.
        all: rewrite ?Z.log2_up_eqn by omega.
        all: try apply Zle_lt_succ.
        all: try apply Z.log2_le_mono.
        all: try omega.
        Local Open Scope Z_scope.
        all: repeat match goal with
                    | [ H : 1 + ?x <= 2 |- _ ] => assert (x <= 1) by omega; clear H
                    | [ H : 1 + ?x <= 1 |- _ ] => assert (x <= 0) by omega; clear H
                    | [ H : (?x <= 1)%Z |- _ ]
                      => is_var x;
                           assert (0 <= x <= 1) by omega;
                           assert (x = 0 \/ x = 1) by omega;
                           destruct_head' or; subst
                    | [ H : ?x + ?y <= 1 |- _ ]
                      => is_var x; is_var y;
                           assert (0 <= x + y <= 1) by omega;
                           assert ((x = 0 /\ y = 0) \/ (x = 0 /\ y = 1) \/ (x = 1 /\ y = 0)) by omega;
                           destruct_head' or; destruct_head' and; subst
                    | [ H : ?x <= 0 |- _ ]
                      => is_var x;
                           assert (x = 0) by omega;
                           destruct_head' or; subst
                    | [ H : ?x <= ?x |- _ ] => clear H
                    | [ H : ?a <= ?b, H' : ?a <= ?b |- _ ] => clear H'
                    | [ H : 0 <= 1 |- _ ] => clear H
                    | _ => progress simpl in *
                    | [ H : 0 <= 0 <= 1 |- _ ] => clear H
                    | [ H : context[0 + _] |- _ ] => rewrite Z.add_0_l in H
                    | [ H : 1 + ?x <= 1 + ?y |- _ ] => assert (x <= y) by omega; clear H
                    | [ H : ?x <= ?x + ?y |- _ ] => assert (0 <= y) by omega; clear H
                    | _ => omega
                    end. }
      { rewrite wadd_def_ZToWord;
          repeat rewrite !wordToZ_ZToWord.
        reflexivity.
        all:try split; try omega.
        all:rewrite ?Z.pow_Zpow, ?Z2Nat.id, ?Nat2Z.inj_succ, ?Nat2Z.inj_0, <- ?Z.one_succ, <- ?Z.two_succ.
        all:auto using Z.log2_up_nonneg.
        all: repeat apply Z.max_case_strong; intros.
        all: try (eapply Z.lt_le_trans; [ | rewrite <- !Z.log2_up_le_full_max; reflexivity ]).
        all: repeat apply Z.max_case_strong; intros.
        all: try (eapply Z.lt_le_trans; [ | rewrite <- !Z.log2_up_le_full_max; reflexivity ]).
        all: repeat apply Z.max_case_strong; intros.
        all: try omega.
        all: change (2^1) with 2 in *.
        all: try omega.
        all:repeat match goal with
                   | [ H : Z.log2_up _ <= 1 |- _ ] => apply Z.log2_up_le_1 in H
                   | [ H : 1 <= Z.log2_up _ |- _ ] => apply Z.log2_up_1_le in H
                   end.
        all: try omega.
        all: rewrite ?Z.log2_up_eqn by omega.
        all: try apply Zle_lt_succ.
        all: try apply Z.log2_le_mono.
        all: try omega.
        all: repeat match goal with
                    | [ H : 1 + ?x <= 2 |- _ ] => assert (x <= 1) by omega; clear H
                    | [ H : 1 + ?x <= 1 |- _ ] => assert (x <= 0) by omega; clear H
                    | [ H : ?x <= 1 |- _ ]
                      => is_var x;
                           assert (0 <= x <= 1) by omega;
                           assert (x = 0 \/ x = 1) by omega;
                           destruct_head' or; subst
                    | [ H : ?x + ?y <= 1 |- _ ]
                      => is_var x; is_var y;
                           assert (0 <= x + y <= 1) by omega;
                           assert ((x = 0 /\ y = 0) \/ (x = 0 /\ y = 1) \/ (x = 1 /\ y = 0)) by omega;
                           destruct_head' or; destruct_head' and; subst
                    | [ H : ?x <= 0 |- _ ]
                      => is_var x;
                           assert (x = 0) by omega;
                           destruct_head' or; subst
                    | [ H : ?x <= ?x |- _ ] => clear H
                    | [ H : ?a <= ?b, H' : ?a <= ?b |- _ ] => clear H'
                    | [ H : 0 <= 1 |- _ ] => clear H
                    | _ => progress simpl in *
                    | [ H : 0 <= 0 <= 1 |- _ ] => clear H
                    | [ H : context[0 + _] |- _ ] => rewrite Z.add_0_l in H
                    | [ H : 1 + ?x <= 1 + ?y |- _ ] => assert (x <= y) by omega; clear H
                    | [ H : ?x <= ?x + ?y |- _ ] => assert (0 <= y) by omega; clear H
                    | _ => omega
                    end. }
      { rewrite wadd_def_ZToWord;
          repeat rewrite !wordToZ_ZToWord.
        reflexivity.
        all:try split; try omega.
        all:rewrite ?Z.pow_Zpow, ?Z2Nat.id, ?Nat2Z.inj_succ, ?Nat2Z.inj_0, <- ?Z.one_succ, <- ?Z.two_succ.
        all:auto using Z.log2_up_nonneg.
        all: repeat apply Z.max_case_strong; intros.
        all: try (eapply Z.lt_le_trans; [ | rewrite <- !Z.log2_up_le_full_max; reflexivity ]).
        all: repeat apply Z.max_case_strong; intros.
        all: try (eapply Z.lt_le_trans; [ | rewrite <- !Z.log2_up_le_full_max; reflexivity ]).
        all: repeat apply Z.max_case_strong; intros.
        all: try omega.
        all: change (2^1) with 2 in *.
        all: try omega.
        all:repeat match goal with
                   | [ H : Z.log2_up _ <= 1 |- _ ] => apply Z.log2_up_le_1 in H
                   | [ H : 1 <= Z.log2_up _ |- _ ] => apply Z.log2_up_1_le in H
                   end.
        all: try omega.
        all: rewrite ?Z.log2_up_eqn by omega.
        all: try apply Zle_lt_succ.
        all: try apply Z.log2_le_mono.
        all: try omega.
        all: repeat match goal with
                    | [ H : 1 + ?x <= 2 |- _ ] => assert (x <= 1) by omega; clear H
                    | [ H : 1 + ?x <= 1 |- _ ] => assert (x <= 0) by omega; clear H
                    | [ H : ?x <= 1 |- _ ]
                      => is_var x;
                           assert (0 <= x <= 1) by omega;
                           assert (x = 0 \/ x = 1) by omega;
                           destruct_head' or; subst
                    | [ H : ?x + ?y <= 1 |- _ ]
                      => is_var x; is_var y;
                           assert (0 <= x + y <= 1) by omega;
                           assert ((x = 0 /\ y = 0) \/ (x = 0 /\ y = 1) \/ (x = 1 /\ y = 0)) by omega;
                           destruct_head' or; destruct_head' and; subst
                    | [ H : ?x <= 0 |- _ ]
                      => is_var x;
                           assert (x = 0) by omega;
                           destruct_head' or; subst
                    | [ H : ?x <= ?x |- _ ] => clear H
                    | [ H : ?a <= ?b, H' : ?a <= ?b |- _ ] => clear H'
                    | [ H : 0 <= 1 |- _ ] => clear H
                    | _ => progress simpl in *
                    | [ H : 0 <= 0 <= 1 |- _ ] => clear H
                    | [ H : context[0 + _] |- _ ] => rewrite Z.add_0_l in H
                    | [ H : 1 + ?x <= 1 + ?y |- _ ] => assert (x <= y) by omega; clear H
                    | [ H : ?x <= ?x + ?y |- _ ] => assert (0 <= y) by omega; clear H
                    | _ => omega
                    end. }
      { rewrite wadd_def_ZToWord;
          repeat rewrite !wordToZ_ZToWord.
        reflexivity.
        all:try split; try omega.
        all:rewrite ?Z.pow_Zpow, ?Z2Nat.id, ?Nat2Z.inj_succ, ?Nat2Z.inj_0, <- ?Z.one_succ, <- ?Z.two_succ.
        all:auto using Z.log2_up_nonneg.
        all: repeat apply Z.max_case_strong; intros.
        all: try (eapply Z.lt_le_trans; [ | rewrite <- !Z.log2_up_le_full_max; reflexivity ]).
        all: repeat apply Z.max_case_strong; intros.
        all: try (eapply Z.lt_le_trans; [ | rewrite <- !Z.log2_up_le_full_max; reflexivity ]).
        all: repeat apply Z.max_case_strong; intros.
        all: try omega.
        all: change (2^1) with 2 in *.
        all: try omega.
        all:repeat match goal with
                   | [ H : Z.log2_up _ <= 1 |- _ ] => apply Z.log2_up_le_1 in H
                   | [ H : 1 <= Z.log2_up _ |- _ ] => apply Z.log2_up_1_le in H
                   end.
        all: try omega.
        all: rewrite ?Z.log2_up_eqn by omega.
        all: try apply Zle_lt_succ.
        all: try apply Z.log2_le_mono.
        all: try omega.
        all: repeat match goal with
                    | [ H : 1 + ?x <= 2 |- _ ] => assert (x <= 1) by omega; clear H
                    | [ H : 1 + ?x <= 1 |- _ ] => assert (x <= 0) by omega; clear H
                    | [ H : ?x <= 1 |- _ ]
                      => is_var x;
                           assert (0 <= x <= 1) by omega;
                           assert (x = 0 \/ x = 1) by omega;
                           destruct_head' or; subst
                    | [ H : ?x + ?y <= 1 |- _ ]
                      => is_var x; is_var y;
                           assert (0 <= x + y <= 1) by omega;
                           assert ((x = 0 /\ y = 0) \/ (x = 0 /\ y = 1) \/ (x = 1 /\ y = 0)) by omega;
                           destruct_head' or; destruct_head' and; subst
                    | [ H : ?x <= 0 |- _ ]
                      => is_var x;
                           assert (x = 0) by omega;
                           destruct_head' or; subst
                    | [ H : ?x <= ?x |- _ ] => clear H
                    | [ H : ?a <= ?b, H' : ?a <= ?b |- _ ] => clear H'
                    | [ H : 0 <= 1 |- _ ] => clear H
                    | _ => progress simpl in *
                    | [ H : 0 <= 0 <= 1 |- _ ] => clear H
                    | [ H : context[0 + _] |- _ ] => rewrite Z.add_0_l in H
                    | [ H : 1 + ?x <= 1 + ?y |- _ ] => assert (x <= y) by omega; clear H
                    | [ H : ?x <= ?x + ?y |- _ ] => assert (0 <= y) by omega; clear H
                    | _ => omega
                    end. } }
  Admitted.

  Lemma is_bounded_by_cast_bound_op G t0 tR (opc : op t0 tR)
        (ein eout ebounds : exprf base_type op t0)
        (HG : forall (t : base_type) (x : Syntax.interp_base_type t) (x' : interp_base_type t),
            List.In (existT _ t (x, x')) G
            -> is_bounded_by' x x')
        (Hwf : wff G ein ebounds)
        (He : interpf Syntax.interp_op ein = interpf Syntax.interp_op eout)
        (Hbounds_are_good : bounds_are_good (interpf (@interp_op) (Op opc ebounds)))
    : is_bounded_by
        (interpf Syntax.interp_op (cast_bound_op opc opc eout (interpf (@interp_op) ebounds)))
        (interpf (@interp_op) (Op opc ebounds)).
  Proof.
    erewrite interpf_cast_bound_op by eassumption.
    simpl; apply is_bounded_by_interp_op.
    eapply interpf_wff; eauto; apply is_bounded_by_interp_op.
  Qed.

  Lemma MapBounds_correct_and_bounded {t}
        (e : Expr base_type op t)
        (Hwf : Wf e)
        (input_bounds : interp_flat_type interp_base_type (domain t))
        (output_bounds := ComputeBounds e input_bounds)
        (e' := MapBounds e input_bounds)
        (Hgood : bounds_are_recursively_good
                   (@interp_op) bound_is_good
                   (invert_Abs (e interp_base_type) input_bounds))
    : forall x y,
      map_uncast_const input_bounds x = y
      -> is_bounded_by y input_bounds
      -> is_bounded_by (Interp (@Syntax.interp_op) e (map_uncast_const _ x)) output_bounds
         /\ mapf_interp_new_flat_typeToZ (Interp (@Syntax.interp_op) e' x)
            = mapf_interpToZ (Interp (@Syntax.interp_op) e y).
  Proof.
    intros x y ? Hb; subst y output_bounds e'.
    unfold MapBounds, ComputeBounds.
    rewrite InterpExprEta.
    rewrite Interp_InlineConstGen by auto with wf.
    rewrite Interp_Linearize.
    rewrite InterpSmartBound by auto with wf.
    erewrite InterpMapInterpCast with (R':=@is_bounded_by')
      by solve [ eauto with wf
               | intros; eapply is_bounded_by_cast_bound_op; eauto
               | intros; eapply interpf_cast_bound_op; eauto ].
    split; [ | reflexivity ].
    eapply InterpWf; eauto; apply is_bounded_by_interp_op.
  Qed.

  Lemma MapBounds_correct_and_bounded_bool {t}
        (e : Expr base_type op t)
        (Hwf : Wf e)
        (input_bounds : interp_flat_type interp_base_type (domain t))
        (output_bounds := ComputeBounds e input_bounds)
        (e' := MapBounds e input_bounds)
        (Hgood : ((bounds_are_recursively_goodb
                     (@interp_op) bound_is_goodb
                     (invert_Abs (e interp_base_type) input_bounds)))%bool
                 = true)
    : forall x,
      is_bounded_by (map_uncast_const input_bounds x) input_bounds
      -> is_bounded_by (Interp (@Syntax.interp_op) e (map_uncast_const _ x)) output_bounds
         /\ mapf_interp_new_flat_typeToZ (Interp (@Syntax.interp_op) e' x)
            = mapf_interpToZ (Interp (@Syntax.interp_op) e (map_uncast_const input_bounds x)).
  Proof.
    intros; eapply MapBounds_correct_and_bounded; eauto.
    { apply bounds_are_recursively_good_iff_bool; assumption. }
  Qed.

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
