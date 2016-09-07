Require Import Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.ArchitectureToZLike.
Require Import Crypto.BoundedArithmetic.ArchitectureToZLikeProofs.
Require Import Crypto.ModularArithmetic.Montgomery.ZBounded.
Require Import Crypto.ModularArithmetic.Montgomery.ZProofs.
Require Import Crypto.Util.Tuple Crypto.Util.Option Crypto.Util.Sigma Crypto.Util.Prod.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Linearize.
Require Import Crypto.Reflection.CommonSubexpressionElimination.
Require Import Crypto.Reflection.Reify.

Local Open Scope Z_scope.
Notation eta x := (fst x, snd x).
Notation eta3 x := (eta (fst x), snd x).
Notation eta3' x := (fst x, eta (snd x)).

Section expression.
  Context (ops : fancy_machine.instructions (2 * 128)) (props : fancy_machine.arithmetic ops) (modulus : Z) (m' : Z) (Hm : modulus <> 0) (H : 0 <= modulus < 2^256) (Hm' : 0 <= m' < 2^256).
  Let H' : 0 <= 256 <= 256. omega. Qed.
  Let H'' : 0 < 256. omega. Qed.
  Let props' := ZLikeProperties_of_ArchitectureBoundedOps ops modulus H 256 H' H''.
  Let ops' := (ZLikeOps_of_ArchitectureBoundedOps ops modulus 256).
  Local Notation fst' := (@fst fancy_machine.W fancy_machine.W).
  Local Notation snd' := (@snd fancy_machine.W fancy_machine.W).
  Definition ldi' : load_immediate
                     (@ZBounded.SmallT (2 ^ 256) (2 ^ 256) modulus
                                       (@ZLikeOps_of_ArchitectureBoundedOps 128 ops modulus 256)) := _.
  Let isldi : is_load_immediate ldi' := _.
  Definition pre_f := (fun v => (reduce_via_partial (2^256) modulus (props := props') (ldi' m') I Hm (fst' v, snd' v))).
  Definition f := (fun v => proj1_sig (pre_f v)).

  Local Arguments proj1_sig _ _ !_ / .
  Local Arguments ZBounded.CarryAdd / .
  Local Arguments ZBounded.ConditionalSubtract / .
  Local Arguments ZBounded.ConditionalSubtractModulus / .
  Local Arguments ZLikeOps_of_ArchitectureBoundedOps / .
  Local Arguments ZBounded.DivBy_SmallBound / .
  Local Arguments f / .
  Local Arguments pre_f / .
  Local Arguments ldi' / .
  Local Arguments reduce_via_partial / .

  Definition expression'
    := Eval simpl in f.
  Definition expression
    := Eval cbv beta delta [expression' fst snd] in
        fun v => let RegMod := fancy_machine.ldi modulus in
                 let RegPInv := fancy_machine.ldi m' in
                 let RegZero := fancy_machine.ldi 0 in
                 expression' v.
  Definition expression_eq v : fancy_machine.decode (expression v) = _
    := proj1 (proj2_sig (pre_f v) I).
  Definition expression_correct
             R' HR0 HR1
             v
             Hv
    : ZUtil.Z.equiv_modulo _ (fancy_machine.decode (expression v)) _
      /\ 0 <= fancy_machine.decode (expression v) < _
    := @ZBounded.reduce_via_partial_correct (2^256) modulus _ props' (ldi' m') I Hm R' HR0 HR1 v I Hv.
End expression.

Section reflection.
  Context (ops : fancy_machine.instructions (2 * 128)).
  Local Set Boolean Equality Schemes.
  Local Set Decidable Equality Schemes.
  Inductive base_type := TZ | Tbool | TW.
  Definition interp_base_type (v : base_type) : Type :=
    match v with
    | TZ => Z
    | Tbool => bool
    | TW => fancy_machine.W
    end.
  Local Notation tZ := (Tbase TZ).
  Local Notation tbool := (Tbase Tbool).
  Local Notation tW := (Tbase TW).
  Local Open Scope ctype_scope.
  Inductive op : flat_type base_type -> flat_type base_type -> Type :=
  | OPldi     : op tZ tW
  | OPshrd    : op (tW * tW * tZ) tW
  | OPshl     : op (tW * tZ) tW
  | OPshr     : op (tW * tZ) tW
  | OPmkl     : op (tW * tZ) tW
  | OPadc     : op (tW * tW * tbool) (tbool * tW)
  | OPsubc    : op (tW * tW * tbool) (tbool * tW)
  | OPmulhwll : op (tW * tW) tW
  | OPmulhwhl : op (tW * tW) tW
  | OPmulhwhh : op (tW * tW) tW
  | OPselc    : op (tbool * tW * tW) tW
  | OPaddm    : op (tW * tW * tW) tW.

  Definition interp_op src dst (f : op src dst)
    : interp_flat_type_gen interp_base_type src -> interp_flat_type_gen interp_base_type dst
    := match f in op s d return interp_flat_type_gen _ s -> interp_flat_type_gen _ d with
       | OPldi     => ldi
       | OPshrd    => fun xyz => let '(x, y, z) := eta3 xyz in shrd x y z
       | OPshl     => fun xy => let '(x, y) := eta xy in shl x y
       | OPshr     => fun xy => let '(x, y) := eta xy in shr x y
       | OPmkl     => fun xy => let '(x, y) := eta xy in mkl x y
       | OPadc     => fun xyz => let '(x, y, z) := eta3 xyz in adc x y z
       | OPsubc    => fun xyz => let '(x, y, z) := eta3 xyz in subc x y z
       | OPmulhwll => fun xy => let '(x, y) := eta xy in mulhwll x y
       | OPmulhwhl => fun xy => let '(x, y) := eta xy in mulhwhl x y
       | OPmulhwhh => fun xy => let '(x, y) := eta xy in mulhwhh x y
       | OPselc    => fun xyz => let '(x, y, z) := eta3 xyz in selc x y z
       | OPaddm    => fun xyz => let '(x, y, z) := eta3 xyz in addm x y z
       end.

  Inductive SConstT := ZConst (_ : Z) | BoolConst (_ : bool) | INVALID_CONST.
  Inductive op_code : Set :=
  | SOPldi | SOPshrd | SOPshl | SOPshr | SOPmkl | SOPadc | SOPsubc
  | SOPmulhwll | SOPmulhwhl | SOPmulhwhh | SOPselc | SOPaddm.

  Definition symbolicify_const (t : base_type) : interp_base_type t -> SConstT
    := match t with
       | TZ => fun x => ZConst x
       | Tbool => fun x => BoolConst x
       | TW => fun x => INVALID_CONST
       end.
  Definition symbolicify_op s d (v : op s d) : op_code
    := match v with
       | OPldi => SOPldi
       | OPshrd => SOPshrd
       | OPshl => SOPshl
       | OPshr => SOPshr
       | OPmkl => SOPmkl
       | OPadc => SOPadc
       | OPsubc => SOPsubc
       | OPmulhwll => SOPmulhwll
       | OPmulhwhl => SOPmulhwhl
       | OPmulhwhh => SOPmulhwhh
       | OPselc => SOPselc
       | OPaddm => SOPaddm
       end.

  Definition CSE {t} e := @CSE base_type SConstT op_code base_type_beq SConstT_beq op_code_beq internal_base_type_dec_bl interp_base_type op symbolicify_const symbolicify_op t e (fun _ => nil).
End reflection.
Section instances.
  Context {ops : fancy_machine.instructions (2 * 128)}.
  Global Instance: forall x, reify_op op (ldi x) 1 OPldi := fun _ => I.
  Global Instance: forall x y z, reify_op op (shrd x y z) 3 OPshrd := fun _ _ _ => I.
  Global Instance: forall x y, reify_op op (shl x y) 2 OPshl := fun _ _ => I.
  Global Instance: forall x y, reify_op op (shr x y) 2 OPshr := fun _ _ => I.
  Global Instance: forall x y, reify_op op (mkl x y) 2 OPmkl := fun _ _ => I.
  Global Instance: forall x y z, reify_op op (adc x y z) 3 OPadc := fun _ _ _ => I.
  Global Instance: forall x y z, reify_op op (subc x y z) 3 OPsubc := fun _ _ _ => I.
  Global Instance: forall x y, reify_op op (mulhwll x y) 2 OPmulhwll := fun _ _ => I.
  Global Instance: forall x y, reify_op op (mulhwhl x y) 2 OPmulhwhl := fun _ _ => I.
  Global Instance: forall x y, reify_op op (mulhwhh x y) 2 OPmulhwhh := fun _ _ => I.
  Global Instance: forall x y z, reify_op op (selc x y z) 3 OPselc := fun _ _ _ => I.
  Global Instance: forall x y z, reify_op op (addm x y z) 3 OPaddm := fun _ _ _ => I.
  Global Instance: reify type Z := TZ.
  Global Instance: reify type bool := Tbool.
  Global Instance: reify type fancy_machine.W := TW.
End instances.
Ltac Reify' e := Reify.Reify' base_type (interp_base_type _) op e.
Ltac Reify e := Reify.Reify base_type (interp_base_type _) op e.
Ltac Reify_rhs := Reify.Reify_rhs base_type (interp_base_type _) op (interp_op _).

Section reflected.
  Context (ops : fancy_machine.instructions (2 * 128)).
  Definition rexpression : Syntax.Expr base_type (interp_base_type _) op (Arrow TZ (Arrow TZ (Arrow TW (Arrow TW (Tbase TW))))).
  Proof.
    let v := (eval cbv beta delta [expression] in (fun modulus m' x y => expression ops modulus m' (x, y))) in
    let v := Reify v in
    exact v.
  Defined.

  Definition rexpression_simple := Eval vm_compute in CSE ops (InlineConst (Linearize rexpression)).
End reflected.

Section syn.
  Context {var : base_type -> Type}.
  Inductive syntax :=
  | RegPInv
  | RegMod
  | RegZero
  | cConstZ : Z -> syntax
  | cConstBool : bool -> syntax
  | cLowerHalf : syntax -> syntax
  | cUpperHalf : syntax -> syntax
  | cLeftShifted : syntax -> Z -> syntax
  | cRightShifted : syntax -> Z -> syntax
  | cVar : var TW -> syntax
  | cVarC : var Tbool -> syntax
  | cBind : syntax -> (var TW -> syntax) -> syntax
  | cBindCarry : syntax -> (var Tbool -> var TW -> syntax) -> syntax
  | cMul128 : syntax -> syntax -> syntax
  | cSelc : var Tbool -> syntax -> syntax -> syntax
  | cAddc : var Tbool -> syntax -> syntax -> syntax
  | cAddm : syntax -> syntax -> syntax
  | cAdd : syntax -> syntax -> syntax
  | cSub : syntax -> syntax -> syntax
  | cPair : syntax -> syntax -> syntax
  | cAbs {t} : (var t -> syntax) -> syntax
  | cINVALID {T} (_ : T).
End syn.

Notation "'Return' x" := (cVar x) (at level 200).
Notation "'c.Mul128' ( x , A , B ) , b" :=
  (cBind (cMul128 A B) (fun x => b))
    (at level 200, b at level 200, format "'c.Mul128' ( x ,  A ,  B ) , '//' b").
Notation "'c.Add' ( x , A , B ) , b" :=
  (cBindCarry (cAdd A B) (fun _ x => b))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' b").
Notation "'c.Add' ( x , A , B ) , b" :=
  (cBindCarry (cAdd (cVar A) B) (fun _ x => b))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , b" :=
  (cBindCarry (cAdd A B) (fun c x => cBindCarry (cAddc c A1 B1) (fun _ x1 => b)))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , b" :=
  (cBindCarry (cAdd A B) (fun c x => cBindCarry (cAddc c (cVar A1) B1) (fun _ x1 => b)))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , b" :=
  (cBindCarry (cAdd (cVar A) B) (fun c x => cBindCarry (cAddc c A1 B1) (fun _ x1 => b)))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , b" :=
  (cBindCarry (cAdd (cVar A) B) (fun c x => cBindCarry (cAddc c (cVar A1) B1) (fun _ x1 => b)))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , 'c.Selc' ( x2 , A2 , B2 ) , b" :=
  (cBindCarry (cAdd A B) (fun c x => cBindCarry (cAddc c A1 B1) (fun c1 x1 => cBind (cSelc c1 A2 B2) (fun x2 => b))))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' 'c.Selc' ( x2 ,  A2 ,  B2 ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , 'c.Selc' ( x2 , A2 , B2 ) , b" :=
  (cBindCarry (cAdd (cVar A) B) (fun c x => cBindCarry (cAddc c A1 B1) (fun c1 x1 => cBind (cSelc c1 A2 B2) (fun x2 => b))))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' 'c.Selc' ( x2 ,  A2 ,  B2 ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , 'c.Selc' ( x2 , A2 , B2 ) , b" :=
  (cBindCarry (cAdd A B) (fun c x => cBindCarry (cAddc c (cVar A1) B1) (fun c1 x1 => cBind (cSelc c1 A2 B2) (fun x2 => b))))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' 'c.Selc' ( x2 ,  A2 ,  B2 ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , 'c.Selc' ( x2 , A2 , B2 ) , b" :=
  (cBindCarry (cAdd (cVar A) B) (fun c x => cBindCarry (cAddc c (cVar A1) B1) (fun c1 x1 => cBind (cSelc c1 A2 B2) (fun x2 => b))))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' 'c.Selc' ( x2 ,  A2 ,  B2 ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , 'c.Selc' ( x2 , A2 , B2 ) , b" :=
  (cBindCarry (cAdd (cVar A) (cVar B)) (fun c x => cBindCarry (cAddc c (cVar A1) (cVar B1)) (fun c1 x1 => cBind (cSelc c1 A2 B2) (fun x2 => b))))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' 'c.Selc' ( x2 ,  A2 ,  B2 ) , '//' b").

Notation "'c.Sub' ( x , A , B ) , b" :=
  (cBindCarry (cSub A B) (fun _ x => b))
    (at level 200, b at level 200, format "'c.Sub' ( x ,  A ,  B ) , '//' b").
Notation "'c.Sub' ( x , A , B ) , b" :=
  (cBindCarry (cSub (cVar A) B) (fun _ x => b))
    (at level 200, b at level 200, format "'c.Sub' ( x ,  A ,  B ) , '//' b").
Notation "'c.Sub' ( x , A , B ) , b" :=
  (cBindCarry (cSub A (cVar B)) (fun _ x => b))
    (at level 200, b at level 200, format "'c.Sub' ( x ,  A ,  B ) , '//' b").
Notation "'c.Sub' ( x , A , B ) , b" :=
  (cBindCarry (cSub (cVar A) (cVar B)) (fun _ x => b))
    (at level 200, b at level 200, format "'c.Sub' ( x ,  A ,  B ) , '//' b").

Notation "'c.Addm' ( x , A , B ) , b" :=
  (cBind (cAddm A B) (fun x => b))
    (at level 200, b at level 200, format "'c.Addm' ( x ,  A ,  B ) , '//' b").
Notation "'c.Addm' ( x , A , B ) , b" :=
  (cBind (cAddm A (cVar B)) (fun x => b))
    (at level 200, b at level 200, format "'c.Addm' ( x ,  A ,  B ) , '//' b").
Notation "'c.Addm' ( x , A , B ) , b" :=
  (cBind (cAddm (cVar A) B) (fun x => b))
    (at level 200, b at level 200, format "'c.Addm' ( x ,  A ,  B ) , '//' b").
Notation "'c.Addm' ( x , A , B ) , b" :=
  (cBind (cAddm (cVar A) (cVar B)) (fun x => b))
    (at level 200, b at level 200, format "'c.Addm' ( x ,  A ,  B ) , '//' b").

Notation "'c.LowerHalf' ( x )" :=
  (cLowerHalf x)
    (at level 200, format "'c.LowerHalf' ( x )").
Notation "'c.LowerHalf' ( x )" :=
  (cLowerHalf (cVar x))
    (at level 200, format "'c.LowerHalf' ( x )").
Notation "'c.UpperHalf' ( x )" :=
  (cUpperHalf x)
    (at level 200, format "'c.UpperHalf' ( x )").
Notation "'c.UpperHalf' ( x )" :=
  (cUpperHalf (cVar x))
    (at level 200, format "'c.UpperHalf' ( x )").
Notation "'c.LeftShifted' { x , v }" :=
  (cLeftShifted x v)
    (at level 200, format "'c.LeftShifted' { x ,  v }").
Notation "'c.LeftShifted' { x , v }" :=
  (cLeftShifted (cVar x) v)
    (at level 200, format "'c.LeftShifted' { x ,  v }").
Notation "'c.RightShifted' { x , v }" :=
  (cRightShifted x v)
    (at level 200, format "'c.RightShifted' { x ,  v }").
Notation "'c.RightShifted' { x , v }" :=
  (cRightShifted (cVar x) v)
    (at level 200, format "'c.RightShifted' { x ,  v }").
Notation "'λ'  x .. y , t" := (cAbs (fun x => .. (cAbs (fun y => t)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Syntax := forall var, @syntax var.

Section assemble.
  Context (ops : fancy_machine.instructions (2 * 128)).

  Section with_var.
    Context {var : base_type -> Type}.

    Fixpoint assemble_syntax_const
             {t}
      : interp_flat_type_gen (interp_base_type _) t -> @syntax var
      := match t return interp_flat_type_gen (interp_base_type _) t -> @syntax var with
         | Tbase TZ => cConstZ
         | Tbase Tbool => cConstBool
         | Tbase t => fun _ => cINVALID t
         | Prod A B => fun xy => cPair (@assemble_syntax_const A (fst xy))
                                       (@assemble_syntax_const B (snd xy))
         end.

    Definition assemble_syntaxf_step
               (assemble_syntaxf : forall {t} (v : @Syntax.exprf base_type (interp_base_type _) op (fun _ => @syntax var) t), @syntax var)
               {t} (v : @Syntax.exprf base_type (interp_base_type _) op (fun _ => @syntax var) t) : @syntax var.
    Proof.
      refine match v return @syntax var with
             | Syntax.Const t x => assemble_syntax_const x
             | Syntax.Var _ x => x
             | Syntax.Op t1 tR op args
               => let v := @assemble_syntaxf t1 args in
                  match op, v with
                  | OPldi    , cConstZ 0 => RegZero
                  | OPldi    , cConstZ v => cINVALID v
                  | OPldi    , RegZero => RegZero
                  | OPldi    , RegMod => RegMod
                  | OPldi    , RegPInv => RegPInv
                  | OPshrd   , _ => cINVALID op
                  | OPshl    , cPair w (cConstZ n) => cLeftShifted w n
                  | OPshr    , cPair w (cConstZ n) => cRightShifted w n
                  | OPmkl    , _ => cINVALID op
                  | OPadc    , cPair (cPair x y) (cVarC c) => cAddc c x y
                  | OPadc    , cPair x (cPair y (cVarC c)) => cAddc c x y
                  | OPadc    , cPair (cPair x y) (cConstBool false) => cAdd x y
                  | OPadc    , cPair x (cPair y (cConstBool false)) => cAdd x y
                  | OPsubc   , cPair (cPair x y) (cConstBool false) => cSub x y
                  | OPsubc   , cPair x (cPair y (cConstBool false)) => cSub x y
                  | OPmulhwll, cPair x y => cMul128 (cLowerHalf x) (cLowerHalf y)
                  | OPmulhwhl, cPair x y => cMul128 (cUpperHalf x) (cLowerHalf y)
                  | OPmulhwhh, cPair x y => cMul128 (cUpperHalf x) (cUpperHalf y)
                  | OPselc   , cPair (cVarC c) (cPair x y) => cSelc c x y
                  | OPselc   , cPair (cPair (cVarC c) x) y => cSelc c x y
                  | OPaddm   , cPair x (cPair y RegMod) => cAddm x y
                  | OPaddm   , cPair (cPair x y) RegMod => cAddm x y
                  | _, _ => cINVALID op
                  end
             | Syntax.Let tx ex _ eC
               => let ex' := @assemble_syntaxf _ ex in
                 let eC' := fun x => @assemble_syntaxf _ (eC x) in
                 let special := match ex' with
                                | RegZero as ex'' | RegMod as ex'' | RegPInv as ex''
                                | cUpperHalf _ as ex'' | cLowerHalf _ as ex''
                                | cLeftShifted _ _ as ex''
                                | cRightShifted _ _ as ex''
                                  => Some ex''
                                | _ => None
                                end in
                 match special, tx return (interp_flat_type_gen _ tx -> _) -> _ with
                 | Some x, Tbase _ => fun eC' => eC' x
                 | _, Tbase TW
                   => fun eC' => cBind ex' (fun x => eC' (cVar x))
                 | _, Prod (Tbase Tbool) (Tbase TW)
                   => fun eC' => cBindCarry ex' (fun c x => eC' (cVarC c, cVar x))
                 | _, _
                   => fun _ => cINVALID (fun x : Prop => x)
                 end eC'
             | Syntax.Pair _ ex _ ey
               => cPair (@assemble_syntaxf _ ex) (@assemble_syntaxf _ ey)
             end.
    Defined.

    Fixpoint assemble_syntaxf {t} v {struct v} : @syntax var
      := @assemble_syntaxf_step (@assemble_syntaxf) t v.
    Fixpoint assemble_syntax {t} (v : @Syntax.expr base_type (interp_base_type _) op (fun _ => @syntax var) t) (args : list (@syntax var)) {struct v}
      : @syntax var
      := match v, args return @syntax var with
         | Syntax.Return _ x, _ => assemble_syntaxf x
         | Syntax.Abs _ _ f, nil => cAbs (fun x => @assemble_syntax _ (f (cVar x)) args)
         | Syntax.Abs _ _ f, cons v vs => @assemble_syntax _ (f v) vs
         end.
  End with_var.

  Definition AssembleSyntax {t} (v : Syntax.Expr _ _ _ t) (args : list Syntax) : Syntax
    := fun var => @assemble_syntax var t (v _) (List.map (fun f => f var) args).
End assemble.

Definition compiled_syntax
  := Eval vm_compute in
      (fun ops => AssembleSyntax ops (rexpression_simple _) (@RegMod :: @RegPInv :: nil)%list).

Print compiled_syntax.
(* compiled_syntax =
fun (_ : fancy_machine.instructions (2 * 128)) (var : base_type -> Type) =>
λ x x0 : var TW,
c.Mul128(x1, c.LowerHalf(x), c.LowerHalf(RegPInv)),
c.Mul128(x2, c.UpperHalf(x), c.LowerHalf(RegPInv)),
c.Add(x4, x1, c.LeftShifted{x2, 128}),
c.Mul128(x5, c.UpperHalf(RegPInv), c.LowerHalf(x)),
c.Add(x7, x4, c.LeftShifted{x5, 128}),
c.Mul128(x8, c.UpperHalf(x7), c.UpperHalf(RegMod)),
c.Mul128(x9, c.UpperHalf(x7), c.LowerHalf(RegMod)),
c.Mul128(x10, c.LowerHalf(x7), c.LowerHalf(RegMod)),
c.Add(x12, x10, c.LeftShifted{x9, 128}),
c.Addc(x14, x8, c.RightShifted{x9, 128}),
c.Mul128(x15, c.UpperHalf(RegMod), c.LowerHalf(x7)),
c.Add(x17, x12, c.LeftShifted{x15, 128}),
c.Addc(x19, x14, c.RightShifted{x15, 128}),
c.Add(_, x, x17),
c.Addc(x23, x0, x19),
c.Selc(x24, RegMod, RegZero),
c.Sub(x26, x23, x24),
c.Addm(x27, x26, RegZero),
Return x27
     : fancy_machine.instructions (2 * 128) -> forall var : base_type -> Type, syntax
*)
