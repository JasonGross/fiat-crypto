Require Import Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.ArchitectureToZLike.
Require Import Crypto.BoundedArithmetic.ArchitectureToZLikeProofs.
Require Import Crypto.ModularArithmetic.BarrettReduction.ZBounded.
Require Import Crypto.ModularArithmetic.BarrettReduction.ZHandbook.
Require Import Crypto.Util.Tuple Crypto.Util.Option Crypto.Util.Sigma Crypto.Util.Prod.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Linearize.
Require Import Crypto.Reflection.CommonSubexpressionElimination.
Require Import Crypto.Reflection.Reify.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Notations.

Local Open Scope Z_scope.
Notation eta x := (fst x, snd x).
Notation eta3 x := (eta (fst x), snd x).
Notation eta3' x := (fst x, eta (snd x)).

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

Section expression.
  Let b : Z := 2.
  Let k : Z := 253.
  Let offset : Z := 3.
  Context (ops : fancy_machine.instructions (2 * 128)) (props : fancy_machine.arithmetic ops).
  (** 25519 dsa *)
  Context (m μ : Z)
          (m_pos : 0 < m).
  Let base_pos : 0 < b. reflexivity. Qed.
  Context (k_good : m < b^k)
          (μ_good : μ = b^(2*k) / m) (* [/] is [Z.div], which is truncated *).
  Let offset_nonneg : 0 <= offset. unfold offset; omega. Qed.
  Let k_big_enough : offset <= k. unfold offset, k; omega. Qed.
  Context (m_small : 3 * m <= b^(k+offset))
          (m_large : b^(k-offset) <= m + 1).
  Context (H : 0 <= m < 2^256).
  Let H' : 0 <= 250 <= 256. omega. Qed.
  Let H'' : 0 < 250. omega. Qed.
  Let props' := ZLikeProperties_of_ArchitectureBoundedOps ops m H 250 H' H''.
  Let ops' := (ZLikeOps_of_ArchitectureBoundedOps ops m 250).
  Local Existing Instances props' ops'.
  Local Notation fst' := (@fst fancy_machine.W fancy_machine.W).
  Local Notation snd' := (@snd fancy_machine.W fancy_machine.W).
  Local Notation SmallT := (@ZBounded.SmallT (2 ^ 256) (2 ^ 250) m
                                  (@ZLikeOps_of_ArchitectureBoundedOps 128 ops m _)).
  Definition ldi' : load_immediate SmallT := _.
  Let isldi : is_load_immediate ldi' := _.
  Axiom (μ_range : 0 <= b ^ (2 * k) / m < b ^ (k + offset)).
  Definition μ' : SmallT := ldi' μ.
  Let μ'_eq : ZBounded.decode_small μ' = μ.
  Proof.
    unfold ZBounded.decode_small, ZLikeOps_of_ArchitectureBoundedOps, μ'.
    apply (decode_load_immediate _ _).
    rewrite μ_good; apply μ_range.
  Qed.

  Definition pre_f v
    := (@barrett_reduce m b k μ offset m_pos base_pos μ_good offset_nonneg k_big_enough m_small m_large ops' props' μ' I μ'_eq (fst' v, snd' v)).

  Local Arguments μ' / .
  Local Arguments ldi' / .

  Definition expression'
    := Eval simpl in
        (fun v => proj1_sig (pre_f v)).
  Definition expression
    := Eval cbv beta iota delta [expression' fst snd] in
        fun v => let RegMod := fancy_machine.ldi m in
              let RegMu := fancy_machine.ldi μ in
              let RegZero := fancy_machine.ldi 0 in
              expression' v.

  Definition expression_eq v H : fancy_machine.decode (expression v) = _
    := proj1 (proj2_sig (pre_f v) H).
End expression.

Print expression.

Section reflected.
  Context (ops : fancy_machine.instructions (2 * 128)).
  Definition rexpression : Syntax.Expr base_type (interp_base_type _) op (Arrow TZ (Arrow TZ (Arrow TW (Arrow TW (Tbase TW))))).
  Proof.
    let v := (eval cbv beta delta [expression] in (fun m μ x y => expression ops m μ (x, y))) in
    let v := Reify v in
    exact v.
  Defined.

  Definition rexpression_simple := Eval vm_compute in CSE ops (InlineConst (Linearize rexpression)).

  Context (m μ : Z)
          (props : fancy_machine.arithmetic ops).

  Let result (v : tuple fancy_machine.W 2) := Syntax.Interp (interp_op _) rexpression_simple m μ (fst v) (snd v).

  Theorem sanity : result = expression ops m μ.
  Proof.
    reflexivity.
  Qed.

  Local Infix "≡₂₅₆" := (Z.equiv_modulo (2^256)).
  Local Infix "≡" := (Z.equiv_modulo m).
  About expression_eq.
  Theorem correctness
          (b : Z := 2)
          (k : Z := 253)
          (offset : Z := 3)
          (H0 : 0 < m)
          (H1 : μ = b^(2 * k) / m)
          (H2 : 3 * m <= b^(k + offset))
          (H3 : b^(k - offset) <= m + 1)
          (H4 : 0 <= m < 2^(k + offset))
          (v : tuple fancy_machine.W 2)
    : fancy_machine.decode (result v) = decode v mod m.
  Proof.
    replace m' with (fancy_machine.decode (fancy_machine.ldi m')) in H4
      by (apply decode_load_immediate; trivial; exact _).
    assert (H' : fancy_machine.decode (result v) ≡ decode v * R'
                 /\ 0 <= fancy_machine.decode (result v) < modulus).
    { rewrite sanity; destruct v; apply expression_correct; assumption. }
    destruct H' as [H'0 H'1].
    rewrite <- H'0.
    rewrite Z.mod_small by assumption.
    reflexivity.
  Qed.
End reflected.

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


Require Import Coq.Classes.RelationClasses Coq.Classes.Morphisms Coq.micromega.Psatz.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.ArchitectureToZLike.
Require Import Crypto.BoundedArithmetic.ArchitectureToZLikeProofs.
Require Import Crypto.ModularArithmetic.BarrettReduction.ZBounded.
Require Import Crypto.Util.Tuple Crypto.Util.Option Crypto.Util.Sigma Crypto.Util.Prod Crypto.Util.ZUtil.
(* These might be needed for faster lookups *)
(*Require Import Coq.FSets.FMaps Coq.FSets.FMapAVL Coq.FSets.FMapFacts Coq.FSets.FMapFullAVL.*)

Require Import Bedrock.Word.
Require Import Crypto.Util.GlobalSettings.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.

Require Import Crypto.Assembly.Evaluables.

Local Open Scope Z_scope.
Notation eta x := (fst x, snd x).
Notation eta3 x := (eta (fst x), snd x).
Notation eta3' x := (fst x, eta (snd x)).

Section fold.
  Context {A B} (f : A -> B) (join : B -> B -> B).
  Fixpoint tuple'_fold {n : nat} : tuple' A n -> B
    := match n with
       | 0%nat => fun v => f v
       | S n' => fun v => join (tuple'_fold (fst v)) (f (snd v))
       end.

  Definition tuple_fold (init : B) {n : nat} : tuple A n -> B
    := match n with
       | 0%nat => fun v => init
       | S n' => tuple'_fold
       end.
End fold.

Let b : Z := 2.
Let k : Z := 253.
Let offset : Z := 3.
(** 25519 dsa *)
Axioms (m μ : Z)
       (m_pos : 0 < m).
Let base_pos : 0 < b. reflexivity. Qed.
Axioms (k_good : m < b^k)
       (μ_good : μ = b^(2*k) / m) (* [/] is [Z.div], which is truncated *).
Let offset_nonneg : 0 <= offset. unfold offset; omega. Qed.
Let k_big_enough : offset <= k. unfold offset, k; omega. Qed.
Axioms (m_small : 3 * m <= b^(k+offset))
       (m_large : b^(k-offset) <= m + 1).
Axioms (ops : fancy_machine.instructions (2 * 128)) (props : fancy_machine.arithmetic ops).
Axiom (H : 0 <= m < 2^256).
Let H' : 0 <= 250 <= 256. omega. Qed.
Let H'' : 0 < 250. omega. Qed.
Let props' := ZLikeProperties_of_ArchitectureBoundedOps ops m H 250 H' H''.
Let ops' := (ZLikeOps_of_ArchitectureBoundedOps ops m 250).
Local Existing Instances props' ops'.
Let fst' := @fst fancy_machine.W fancy_machine.W.
Let snd' := @snd fancy_machine.W fancy_machine.W.
Let SmallT := (@ZBounded.SmallT (2 ^ 256) (2 ^ 250) m
                                (@ZLikeOps_of_ArchitectureBoundedOps 128 ops m _)).
Let ldi : load_immediate SmallT := _.
Let isldi : is_load_immediate ldi := _.
Axiom (μ_range : 0 <= b ^ (2 * k) / m < b ^ (k + offset)).
Let μ' : SmallT := ldi μ.
Let μ'_eq : ZBounded.decode_small μ' = μ.
Proof.
  unfold ZBounded.decode_small, ZLikeOps_of_ArchitectureBoundedOps, μ'.
  apply (decode_load_immediate _ _).
  rewrite μ_good; apply μ_range.
Qed.

Let f := (fun v => proj1_sig (@barrett_reduce m b k μ offset m_pos base_pos μ_good offset_nonneg k_big_enough m_small m_large ops' props' μ' I μ'_eq (fst' v, snd' v))).

Section Definitions.
  Inductive vartype := Tbool | TW.
  Inductive consttype := TZ | Tvar (_ : vartype).
  Inductive flat_type := Tconst (_ : consttype) | Prod (_ _ : flat_type).
  Inductive type := Tflat (_ : flat_type) | Arrow : vartype -> type -> type.
  Global Coercion Tvar : vartype >-> consttype.
  Global Coercion Tconst : consttype >-> flat_type.
  Global Coercion Tflat : flat_type >-> type.

  Fixpoint interp_flat_type (t:flat_type): Type :=
    match t with
    | Prod a b => prod (interp_flat_type a) (interp_flat_type b)
    | TZ => Z
    | TW => fancy_machine.W
    | Tbool => bool
    end.

  Fixpoint interp_type (t:type): Type :=
    match t with
    | Arrow a b => interp_flat_type a -> interp_type b
    | Tflat t => interp_flat_type t
    end.

  Section ind.
    Local Notation TZ := (Tconst TZ).
    Local Notation TW := (Tconst TW).
    Local Notation Tbool := (Tconst Tbool).
    Inductive nop : forall (narg nret : nat), tuple flat_type narg -> tuple flat_type nret -> Type :=
    | OPldi     : nop 1 1 TZ TW
    | OPshrd    : nop 3 1 (TW, TW, TZ) TW
    | OPshl     : nop 2 1 (TW, TZ) TW
    | OPshr     : nop 2 1 (TW, TZ) TW
    | OPmkl     : nop 2 1 (TW, TZ) TW
    | OPadc     : nop 3 2 (TW, TW, Tbool) (Tbool, TW)
    | OPsubc    : nop 3 2 (TW, TW, Tbool) (Tbool, TW)
    | OPmulhwll : nop 2 1 (TW, TW) TW
    | OPmulhwhl : nop 2 1 (TW, TW) TW
    | OPmulhwhh : nop 2 1 (TW, TW) TW
    | OPselc    : nop 3 1 (Tbool, TW, TW) TW
    | OPaddm    : nop 3 1 (TW, TW, TW) TW.
  End ind.

  Definition interp_nop {narg nret t1 t2} (op:@nop narg nret t1 t2)
    : tuple_fold interp_flat_type prod unit t1
      -> tuple_fold interp_flat_type prod unit t2
    := match op in (@nop narg nret t1 t2)
             return tuple_fold interp_flat_type prod unit t1
                    -> tuple_fold interp_flat_type prod unit t2
       with
       | OPldi => fun args => ldi args
       | OPshrd => fun args => let '(x1, x2, x3) := eta3 args in shrd x1 x2 x3
       | OPshl => fun args => let '(x1, x2) := eta args in shl x1 x2
       | OPshr => fun args => let '(x1, x2) := eta args in shr x1 x2
       | OPmkl => fun args => let '(x1, x2) := eta args in mkl x1 x2
       | OPadc => fun args => let '(x1, x2, x3) := eta3 args in adc x1 x2 x3
       | OPsubc => fun args => let '(x1, x2, x3) := eta3 args in subc x1 x2 x3
       | OPmulhwll => fun args => let '(x1, x2) := eta args in mulhwll x1 x2
       | OPmulhwhl => fun args => let '(x1, x2) := eta args in mulhwhl x1 x2
       | OPmulhwhh => fun args => let '(x1, x2) := eta args in mulhwhh x1 x2
       | OPselc => fun args => let '(x1, x2, x3) := eta3 args in selc x1 x2 x3
       | OPaddm => fun args => let '(x1, x2, x3) := eta3 args in addm x1 x2 x3
       end.
End Definitions.

Inductive SpecialZConst : Set := Cm | Cμ.
Fixpoint interp_SpecialZConst (e: SpecialZConst) : Z :=
  match e with Cm => m | Cμ => μ end.
Definition all_SpecialZConst : list SpecialZConst := (Cm::Cμ::nil)%list.

Module Input.
  Section Language.
    Section expr.
      Context {var : flat_type -> Type}.

      Inductive expr : type -> Type :=
      | Const : forall {t : flat_type}, interp_type t -> expr t
      | SpZConst : SpecialZConst -> expr TZ
      | Var : forall {t}, var t -> expr t
      | Unop : forall {t1 t2}, @nop 1 1 t1 t2
                               -> expr t1 -> expr (tuple_fold id Prod TZ t2)
      | Binop : forall {t10 t11 t2}, @nop 2 1 (t10, t11) t2
                                     -> expr t10 -> expr t11 -> expr (tuple_fold id Prod TZ t2)
      | Trinop : forall {t10 t11 t12 t2}, @nop 3 1 (t10, t11, t12) t2
                                          -> expr t10 -> expr t11 -> expr t12 -> expr (tuple_fold id Prod TZ t2)
      | Trinop2Ret : forall {t10 t11 t12 t2}, @nop 3 2 (t10, t11, t12) t2
                                              -> expr t10 -> expr t11 -> expr t12 -> expr (tuple_fold id Prod TZ t2)
      | Let : forall {tx : flat_type}, expr tx -> forall {tC}, (var tx -> expr tC) -> expr tC
      | Pair : forall {t1 : flat_type}, expr t1 -> forall {t2 : flat_type}, expr t2 -> expr (Prod t1 t2)
      | Abs : forall {t1 : vartype} {t2}, (var t1 -> expr t2) -> expr (Arrow t1 t2)
      | MatchPair : forall {t1 t2}, expr (Prod t1 t2) -> forall {tC}, (var t1 -> var t2 -> expr tC) -> expr tC.
    End expr.

    Definition Expr t : Type := forall var, @expr var t.

    Fixpoint interp {t} (e: @expr interp_type t) : interp_type t :=
      match e in @expr _ t return interp_type t with
      | Const _ n => n
      | SpZConst n => interp_SpecialZConst n
      | Var _ n => n
      | Unop _ _ op e1 => interp_nop op (interp e1)
      | Binop _ _ _ op e1 e2 => interp_nop op (interp e1, interp e2)
      | Trinop _ _ _ _ op e1 e2 e3 => interp_nop op (interp e1, interp e2, interp e3)
      | Trinop2Ret _ _ _ _ op e1 e2 e3 => interp_nop op (interp e1, interp e2, interp e3)
      | Let _ ex _ eC => let x := interp ex in interp (eC x)
      | Pair _ e1 _ e2 => (interp e1, interp e2)
      | Abs _ _ f => fun x => interp (f x)
      | MatchPair _ _ ep _ eC => let (v1, v2) := interp ep in interp (eC v1 v2)
      end.

    Definition Interp {t} (E:Expr t) : interp_type t := interp (E interp_type).
  End Language.

  (* Reification assumes the argument type is Z *)

  Ltac reify_type t :=
    lazymatch t with
    | BinInt.Z => TZ
    | bool => Tbool
    | fancy_machine.W => TW
    | prod ?l ?r =>
      let l := reify_type l in
      let r := reify_type r in
      constr:(Prod l r)
    | ?l -> ?r =>
      let l := reify_type l in
      let r := reify_type r in
      constr:(Arrow l r)
    end.

  Ltac reify_nop op :=
    lazymatch op with
    | @Interface.ldi     => OPldi
    | @Interface.shrd    => OPshrd
    | @Interface.shl     => OPshl
    | @Interface.shr     => OPshr
    | @Interface.mkl     => OPmkl
    | @Interface.adc     => OPadc
    | @Interface.subc    => OPsubc
    | @Interface.mulhwll => OPmulhwll
    | @Interface.mulhwhl => OPmulhwhl
    | @Interface.mulhwhh => OPmulhwhh
    | @Interface.selc    => OPselc
    | @Interface.addm    => OPaddm
    end.

  Class reify {varT} (var:varT) {eT} (e:eT) {T:Type} := Build_reify : T.
  Definition reify_var_for_in_is {T} (x:T) (t:flat_type) {eT} (e:eT) := False.

  Class absify {eT} (e:eT) {T:Type} := Build_absify : T.

  Local Ltac cidtac e := constr:(ltac:(idtac e; exact I)).
  Ltac reify var e :=
    lazymatch e with
    | let x := ?ex in @?eC x =>
      let ex := reify var ex in
      let eC := reify var eC in
      constr:(Let (var:=var) ex eC)
    | match ?ep with (v1, v2) => @?eC v1 v2 end =>
      let ep := reify var ep in
      let eC := reify var eC in
      constr:(MatchPair (var:=var) ep eC)
    | pair ?a ?b =>
      let a := reify var a in
      let b := reify var b in
      constr:(Pair (var:=var) a b)
    | (fun x : ?T => ?C) =>
      let t := reify_type T in
      (* Work around Coq 8.5 and 8.6 bug *)
      (* <https://coq.inria.fr/bugs/show_bug.cgi?id=4998> *)
      (* Avoid re-binding the Gallina variable referenced by Ltac [x] *)
      (* even if its Gallina name matches a Ltac in this tactic. *)
      let maybe_x := fresh x in
      let not_x := fresh x in
      let C := lazymatch constr:(fun (x : T) (not_x : var t) (_:reify_var_for_in_is x t not_x) =>
                                   (_ : reify var C)) (* [C] here is an open term that references "x" by name *)
               with fun _ v _ => @?C v => C end in
      C
    | m => constr:(SpZConst (var := var) Cm)
    | μ => constr:(SpZConst (var := var) Cμ)
    | ?x
      => lazymatch goal with
         | _:reify_var_for_in_is x ?t ?v |- _ => constr:(@Var var t v)
         | _
           => let op := head x in
              let op := match x with
                        | _ => reify_nop op
                        | _ => let t := (let t := type of x in reify_type t) in
                               constr:(@Const var t x)
                        end in
              lazymatch op with
              | @Const _ _ _ => op
              | _
                => let op := match constr:(Set) with
                             | _ => constr:(Unop (var:=var) op)
                             | _ => constr:(Binop (var:=var) op)
                             | _ => constr:(Trinop (var:=var) op)
                             | _ => constr:(Trinop2Ret (var:=var) op)
                             end in
                   lazymatch op with
                   | Unop _ => lazymatch x with
                               | ?op' ?a
                                 => let a := reify var a in
                                    constr:(op a)
                               end
                   | Binop _ => lazymatch x with
                                | ?op' ?a ?b
                                  => let a := reify var a in
                                     let b := reify var b in
                                     constr:(op a b)
                                end
                   | Trinop _ => lazymatch x with
                                 | ?op' ?a ?b ?c
                                   => let a := reify var a in
                                      let b := reify var b in
                                      let c := reify var c in
                                      constr:(op a b c)
                                 end
                   | Trinop2Ret _ => lazymatch x with
                                     | ?op' ?a ?b ?c
                                       => let a := reify var a in
                                          let b := reify var b in
                                          let c := reify var c in
                                          constr:(op a b c)
                                     end
                   end
              end
         end
    end.
  Local Ltac idtac_goal := match goal with |- ?G => idtac "Goal:" G end.
  Hint Extern 0 (reify ?var ?e) => (let e := reify var e in eexact e) : typeclass_instances.

  Ltac Reify e :=
    lazymatch constr:(fun (var:flat_type->Type) => (_:reify var e)) with
      (fun var => ?C) => constr:(fun (var:flat_type->Type) => C) (* copy the term but not the type cast *)
    end.

  Definition example_expr var : expr (var:=var) (Arrow TW (Arrow TW TW)).
  Proof.
    let f' := (eval cbv [μ' f] in (fun x y => f (x, y))) in
    let f' := (eval simpl in f') in
    let f' := (eval unfold fst', snd', fst, snd in f') in
    let rv := reify var f' in
    let rv := constr:(Abs (fun x => Abs (fun y => rv x y))) in
    let rv := (eval cbv beta in rv) in
    exact rv.
  Defined.

  Definition example_Expr : Expr (Arrow TW (Arrow TW TW))
    := example_expr.

  Lemma example_expr_good : interp (@example_expr _) = (fun x y => f (x, y)).
  Proof.
    cbv [Interp interp example_expr fst snd interp_nop].
    unfold f; simpl.
    reflexivity.
  Qed.

  Lemma example_Expr_good : Interp example_Expr = (fun x y => f (x, y)).
  Proof.
    apply example_expr_good.
  Qed.

  Ltac lhs_of_goal := match goal with |- ?R ?LHS ?RHS => constr:(LHS) end.
  Ltac rhs_of_goal := match goal with |- ?R ?LHS ?RHS => constr:(RHS) end.

  (*Ltac Reify_rhs :=
    let rhs := rhs_of_goal in
    let RHS := Reify rhs in
    transitivity (ZInterp RHS);
    [|cbv iota beta delta [ZInterp Interp interp_type interp_binop interp]; reflexivity].

  Goal (0 = let x := 1+2 in x*3)%Z.
    Reify_rhs.
  Abort.

  Goal (0 = let x := 1 in let y := 2 in x * y)%Z.
    Reify_rhs.
  Abort.*)

  Section wf.
    Context {var1 var2 : flat_type -> Type}.

    Local Notation "x ≡ y" := (existT _ _ (x, y)).

    Inductive wf : list (sigT (fun t => var1 t * var2 t))%type -> forall {t}, @expr var1 t -> @expr var2 t -> Prop :=
    | WfConst : forall G t n, wf G (Const (t := t) n) (Const n)
    | WfSpZConst : forall G n, wf G (SpZConst n) (SpZConst n)
    | WfVar : forall G (t : flat_type) x x', In (x ≡ x') G -> @wf G t (Var x) (Var x')
    | WfUnop : forall G {t1 t2} (op : nop 1 1 t1 t2) (e1:@expr var1 t1) (e1':@expr var2 t1),
        wf G e1 e1'
        -> wf G (Unop op e1) (Unop op e1')
    | WfBinop : forall G {t10 t11 t2} (op : nop 2 1 (t10, t11) t2)
                       (e10:@expr var1 t10) (e11:@expr var1 t11)
                       (e10':@expr var2 t10) (e11':@expr var2 t11),
        wf G e10 e10'
        -> wf G e11 e11'
        -> wf G (Binop op e10 e11) (Binop op e10' e11')
    | WfTrinop : forall G {t10 t11 t12 t2} (op : nop 3 1 (t10, t11, t12) t2)
                       (e10:@expr var1 t10) (e11:@expr var1 t11) (e12:@expr var1 t12)
                       (e10':@expr var2 t10) (e11':@expr var2 t11) (e12':@expr var2 t12),
        wf G e10 e10'
        -> wf G e11 e11'
        -> wf G e12 e12'
        -> wf G (Trinop op e10 e11 e12) (Trinop op e10' e11' e12')
    | WfTrinop2Ret : forall G {t10 t11 t12 t2} (op : nop 3 2 (t10, t11, t12) t2)
                       (e10:@expr var1 t10) (e11:@expr var1 t11) (e12:@expr var1 t12)
                       (e10':@expr var2 t10) (e11':@expr var2 t11) (e12':@expr var2 t12),
        wf G e10 e10'
        -> wf G e11 e11'
        -> wf G e12 e12'
        -> wf G (Trinop2Ret op e10 e11 e12) (Trinop2Ret op e10' e11' e12')
    | WfLet : forall G t1 t2 e1 e1' (e2 : _ t1 -> @expr _ t2) e2',
        wf G e1 e1'
        -> (forall x1 x2, wf ((x1 ≡ x2) :: G) (e2 x1) (e2' x2))
        -> wf G (Let e1 e2) (Let e1' e2')
    | WfAbs : forall G t1 t2 e e',
        (forall x1 x2, wf ((x1 ≡ x2) :: G) (e x1) (e' x2))
        -> wf G (@Abs _ t1 t2 e) (Abs e')
    | WfPair : forall G {t1 t2 : flat_type} (e1: @expr var1 t1) (e2: @expr var1 t2)
                      (e1': @expr var2 t1) (e2': @expr var2 t2),
        wf G e1 e1'
        -> wf G e2 e2'
        -> wf G (Pair e1 e2) (Pair e1' e2')
    | WfMatchPair : forall G t1 t2 tC ep ep' (eC : _ t1 -> _ t2 -> @expr _ tC) eC',
        wf G ep ep'
        -> (forall x1 x2 y1 y2, wf ((x1 ≡ x2) :: (y1 ≡ y2) :: G) (eC x1 y1) (eC' x2 y2))
        -> wf G (MatchPair ep eC) (MatchPair ep' eC').
  End wf.

  Definition Wf {t} (E : @Expr t) := forall var1 var2, wf nil (E var1) (E var2).

  Example example_Expr_Wf : Wf example_Expr.
  Proof.
    repeat match goal with
           | [ |- Wf _ ] => unfold Wf; intros
           | [ |- wf _ _ _ ] => constructor
           | [ |- In ?x (cons ?x _) ] => constructor 1; reflexivity
           | [ |- In _ _ ] => progress unfold tuple'_fold, id, fst, snd
           | [ |- In ?x (cons _ ?xs) ]
             => match xs with context[x] => constructor 2 end
           | _ => intros
           end.
  Qed.

  (*Axiom Wf_admitted : forall {t} (E:Expr t), @Wf Z t E.
  Ltac admit_Wf := apply Wf_admitted.*)
End Input.

Module Output.

  Section Language.
    (* A very restricted language where binary operations are restricted
    to returning [T] and must appear in [let] binders, and all pairs
    must be constructed in the return clause.  No matching on pairs is
    allowed *)

    Section expr.
      Context {var : vartype -> Type}.

      Inductive arg : flat_type -> Type :=
      | Const {t} : @interp_type (Tconst t) -> arg t
      | SpZConst : SpecialZConst -> arg TZ
      | Var {t} : var t -> arg t
      | Pair : forall {t1}, arg t1 -> forall {t2}, arg t2 -> arg (Prod t1 t2).

      Inductive expr : type -> Type :=
      | LetUnop : forall {t1}, nop 1 1 t1 TW -> arg t1 ->
                               forall {tC}, (var TW -> expr tC) -> expr tC
      | LetBinop : forall {t1 t2}, nop 2 1 (t1, t2) TW -> arg t1 -> arg t2 ->
                                   forall {tC}, (var TW -> expr tC) -> expr tC
      | LetTrinop : forall {t1 t2 t3}, nop 3 1 (t1, t2, t3) TW -> arg t1 -> arg t2 -> arg t3 ->
                                       forall {tC}, (var TW -> expr tC) -> expr tC
      | LetTrinop2Ret : forall {t1 t2 t3}, nop 3 2 (t1, t2, t3) (Tconst Tbool, Tconst TW)
                                           -> arg t1 -> arg t2 -> arg t3 ->
                                           forall {tC}, (var Tbool -> var TW -> expr tC) -> expr tC
      | Abs : forall {t1 : vartype} {t2}, (var t1 -> expr t2) -> expr (Arrow t1 t2)
      | Return : forall {t}, arg t -> expr t.
    End expr.

    Arguments arg _ _ : clear implicits.
    Arguments expr _ _ : clear implicits.

    Definition Expr t : Type := forall var, expr var t.

    Fixpoint simple_arg_type (t : type) : flat_type
      := match t with
         | Arrow _ t => simple_arg_type t
         | Tflat t => t
         end.
    Fixpoint under_arrows (t1 : type) (tf : flat_type -> type) :=
      match t1 with
      | Arrow s d => Arrow s (under_arrows d tf)
      | Tflat t => tf t
      end.
    Definition simple_arg {var} t := @arg var (simple_arg_type t).
    Arguments simple_arg _ _ : clear implicits.
    Coercion simple_arg_of_arg {var t} (x : arg var t) : simple_arg var t
      := x.

    Fixpoint interp_arg {t} (e: arg interp_type t) : interp_type t :=
      match e with
      | Const _ n => n
      | SpZConst n => interp_SpecialZConst n
      | Var _ n => n
      | Pair _ e1 _ e2 => (interp_arg e1, interp_arg e2)
      end.

    Fixpoint interp {t} (e:expr interp_type t) : interp_type t :=
      match e with
      | LetUnop _ op a _ eC
        => let x := interp_nop op (interp_arg a) in interp (eC x)
      | LetBinop _ _ op a b _ eC
        => let x := interp_nop op (interp_arg a, interp_arg b) in interp (eC x)
      | LetTrinop _ _ _ op a b c _ eC
        => let x := interp_nop op (interp_arg a, interp_arg b, interp_arg c) in interp (eC x)
      | LetTrinop2Ret _ _ _ op a b c _ eC
        => let '(c, v) := eta (interp_nop op (interp_arg a, interp_arg b, interp_arg c)) in interp (eC c v)
      | Abs _ _ f => fun x => @interp _ (f x)
      | Return _ a => interp_arg a
      end.

    Definition Interp {t} (E:Expr t) : interp_type t := interp (E interp_type).
  End Language.

  Section arg_map.
    Fixpoint map_arg {var1 var2} (f : forall x, var1 x -> var2 x) {t} (v : @arg var1 t) : @arg var2 t
      := match v in @arg _ t return @arg _ t with
         | Const _ x => Const x
         | SpZConst x => SpZConst x
         | Var _ v => Var (f _ v)
         | Pair _ x _ y => Pair (map_arg f x) (map_arg f y)
         end.
  End arg_map.

  Section under_lets.
    Context {var: vartype -> Type}.

    Arguments arg _ _ : clear implicits.
    Arguments simple_arg _ _ : clear implicits.
    Arguments expr _ _ : clear implicits.

    Fixpoint under_lets {t} (e: expr var t) {struct e} :
      forall {tC} (C:simple_arg var t -> expr var tC), expr var (under_arrows t (fun _ => tC))
      := match e in (expr _ t) return forall {tC} (C:simple_arg var t -> expr var tC), expr var (under_arrows t (fun _ => tC)) with
         | LetUnop _ op a _ eC
           => fun tC C => LetUnop op a (fun v => @under_lets _ (eC v) _ C)
         | LetBinop _ _ op a b _ eC
           => fun tC C => LetBinop op a b (fun v => @under_lets _ (eC v) _ C)
         | LetTrinop _ _ _ op a b c _ eC
           => fun tC C => LetTrinop op a b c (fun v => @under_lets _ (eC v) _ C)
         | LetTrinop2Ret _ _ _ op a b c _ eC
           => fun tC C => LetTrinop2Ret op a b c (fun v0 v1 => @under_lets _ (eC v0 v1) _ C)
         | Abs _ _ f
           => fun tC C => Abs (fun x => @under_lets _ (f x) tC C)
         | Return _ a
           => fun _ C => C a
         end.

    Fixpoint under_lets_no_abs {t} (e: expr var t) {struct e} :
      forall {tC} (C:match t with
                     | Arrow _ _ => expr var t
                     | Tflat t => arg var t
                     end -> expr var tC), expr var tC
      := match e in (expr _ t) return forall {tC} (C:match t with
                                                     | Arrow _ _ => expr var t
                                                     | Tflat t => arg var t
                                                     end -> expr var tC), expr var tC with
         | LetUnop _ op a _ eC
           => fun tC C => LetUnop op a (fun v => @under_lets_no_abs _ (eC v) _ C)
         | LetBinop _ _ op a b _ eC
           => fun tC C => LetBinop op a b (fun v => @under_lets_no_abs _ (eC v) _ C)
         | LetTrinop _ _ _ op a b c _ eC
           => fun tC C => LetTrinop op a b c (fun v => @under_lets_no_abs _ (eC v) _ C)
         | LetTrinop2Ret _ _ _ op a b c _ eC
           => fun tC C => LetTrinop2Ret op a b c (fun v0 v1 => @under_lets_no_abs _ (eC v0 v1) _ C)
         | Abs _ _ f as e
           => fun tC C => C e
         | Return _ a
           => fun _ C => C a
         end.
  End under_lets.

  Fixpoint interp_under_arrows t1 {t} (e : @expr _ t) : interp_type (under_arrows t1 (fun _ => t))
    := match t1 with
       | Arrow s d => fun _ => @interp_under_arrows d t e
       | _ => interp e
       end.
  Fixpoint interp_simple_arg {t} (e : @simple_arg _ t) : interp_type t
    := match t return @simple_arg _ t -> interp_type t with
       | Arrow s d => fun e _ => @interp_simple_arg d e
       | Tflat t => fun e => interp_arg e
       end e.
  Fixpoint pointwise_eq_interp {t} : forall (f g : interp_type t), Prop
    := match t return forall (f g : interp_type t), Prop with
       | Arrow s d => fun f g => forall x, @pointwise_eq_interp d (f x) (g x)
       | Tflat _ => fun f g => f = g
       end.
  Fixpoint eq_interp_under_arrows {t1 t} : forall (f g : interp_type (under_arrows t1 t)), Prop
    := match t1 return forall (f g : interp_type (under_arrows t1 t)), Prop with
       | Arrow s d => fun f g => forall x, @eq_interp_under_arrows d t (f x) (g x)
       | Tflat _ => pointwise_eq_interp
       end.
  Module Export Instances.
    Global Instance pointwise_eq_interp_Reflexive {t} : Reflexive (@pointwise_eq_interp t) | 1.
    Proof. induction t; intro x; simpl in *; try reflexivity. Qed.
    Global Instance eq_interp_under_arrows_Reflexive {t1 t} : Reflexive (@eq_interp_under_arrows t1 t) | 1.
    Proof. induction t1; intro x; simpl in *; try reflexivity. Qed.
    Global Instance pointwise_eq_interp_Transitive {t} : Transitive (@pointwise_eq_interp t) | 1.
    Proof. induction t; intros ???; simpl in *; eauto using eq_trans, transitivity. Qed.
    Global Instance eq_interp_under_arrows_Transitive {t1 t} : Transitive (@eq_interp_under_arrows t1 t) | 1.
    Proof. induction t1; intros ???; simpl in *; etransitivity; eauto. Qed.
    Global Instance pointwise_eq_interp_Symmetric {t} : Symmetric (@pointwise_eq_interp t) | 1.
    Proof. induction t; intros ??; simpl in *; eauto using eq_sym, symmetry. Qed.
    Global Instance eq_interp_under_arrows_Symmetric {t1 t} : Symmetric (@eq_interp_under_arrows t1 t) | 1.
    Proof. induction t1; intros ??; simpl in *; symmetry; eauto. Qed.
    Global Instance pointwise_eq_interp_Proper {t}
      : Proper (@pointwise_eq_interp t ==> @pointwise_eq_interp t ==> Basics.flip Basics.impl)
               (@Output.pointwise_eq_interp t).
    Proof.
      intros ?? H ?? H' H''.
      repeat first [ assumption
                   | symmetry; assumption
                   | etransitivity; try eassumption; [] ].
    Qed.
  End Instances.

  Lemma under_lets_correct {t} (e: @expr _ t) {tC}
    (C: @simple_arg _ t -> @expr _ tC)
    (C_Proper : forall a1 a2, interp_arg a1 = interp_arg a2 -> interp (C a1) = interp (C a2)) :
    forall a, interp_simple_arg a = interp e -> eq_interp_under_arrows (interp (under_lets e C)) (interp_under_arrows t (C a)).
  Proof.
    induction e;
      repeat (intuition (congruence || eauto) + simpl in * + rewrite_hyp !* + break_match
              + match goal with H : _ |- _ => progress eauto using (fun x => f_equal (fun f => f x) H) end
              + reflexivity
              + (erewrite_hyp *; [ reflexivity | first [ eassumption | symmetry; eassumption ] ])).
  Qed.

  Local Notation expr_or_arg t := (match t with
                                   | Arrow _ _ => @expr interp_type t
                                   | Tflat t' => @arg interp_type t'
                                   end).
  Definition interp_expr_or_arg {t} (e : expr_or_arg t) : interp_type t
    := match t return expr_or_arg t -> interp_type t with
       | Arrow _ _ => interp
       | Tflat _ => interp_arg
       end e.

  Lemma under_lets_no_abs_correct_pointwise {t} (e: @expr _ t) {tC}
        (C: expr_or_arg t -> @expr _ tC)
    (C_Proper : forall a1 a2, pointwise_eq_interp (interp_expr_or_arg a1) (interp_expr_or_arg a2) -> pointwise_eq_interp (interp (C a1)) (interp (C a2))) :
    forall a, pointwise_eq_interp (interp_expr_or_arg a) (interp e) -> pointwise_eq_interp (interp (under_lets_no_abs e C)) (interp (C a)).
  Proof.
    induction e;
      repeat (intuition (congruence || eauto || reflexivity) + ( simpl in * ) + break_match
              + (rewrite_hyp *; []) + (rewrite_hyp *; [ reflexivity | ])
              + match goal with H : _ |- _ => progress eauto using (fun x => f_equal (fun f => f x) H) end).
  Qed.

  Lemma under_lets_correct_pointwise {t} (e: @expr _ t) {tC}
    (C: @simple_arg _ t -> @expr _ tC)
    (C_Proper : forall a1 a2, pointwise_eq_interp (interp_arg a1) (interp_arg a2) -> pointwise_eq_interp (interp (C a1)) (interp (C a2))) :
    forall a, pointwise_eq_interp (interp_simple_arg a) (interp e) -> eq_interp_under_arrows (interp (under_lets e C)) (interp_under_arrows t (C a)).
  Proof.
    induction e;
      try solve [ repeat (intuition (congruence || eauto) + simpl in * + rewrite_hyp !* + break_match
              + match goal with H : _ |- _ => progress eauto using (fun x => f_equal (fun f => f x) H) end) ].
  Qed.

  Section match_arg.
    Context {var:vartype -> Type}.

    Arguments arg _ _ : clear implicits.
    Arguments simple_arg _ _ : clear implicits.
    Arguments expr _ _ : clear implicits.

    Definition match_arg_Prod' {t1} {t2} (a:arg var (Prod t1 t2)) : option (arg var t1 * arg var t2) :=
      match a in arg _ t
        return option (match t with | Prod _ _ => _ | _ => False end) with
      | Pair _ a1 _ a2 => Some (a1, a2)
      | _ => None
      end.

    Definition match_arg_Prod {t1} {t2} (a:arg var (Prod t1 t2)) : (arg var t1 * arg var t2).
      refine match match_arg_Prod' a with
      | Some (a1, a2) => (a1, a2)
      | None => _ (* impossible *)
      end.
    Proof.
      intros; constructor;
        abstract (repeat match goal with
        | [a: interp_type _ |- _] => destruct a; constructor; assumption
        | [a: arg _ (Prod _ _) |- _] => inversion_clear a; try assumption
        end).
    Defined.

    Global Arguments match_arg_Prod / : simpl nomatch.

    Definition match_arg_Prod_Pair {t1 t2} (a1:arg var t1) (a2:arg var t2) :
      match_arg_Prod (Pair a1 a2) = (a1, a2) := eq_refl.

    Lemma match_arg_Prod_correct_helper {t} (a:arg var t) :
      match t return arg var t -> Prop with
      | Prod _ _ => fun a => forall a1 a2, match_arg_Prod a = (a1, a2) <-> a = Pair a1 a2
      | _ => fun _ => True
      end a.
    Proof.
      unfold match_arg_Prod; destruct a;
        repeat match goal with
        | _ => split
        | _ => intro
        | _ => progress simpl in *
        | _ => break_match
        | _ => intuition congruence
        | H: _ |- _ => eapply (f_equal match_arg_Prod) in H
        end.
    Qed.

    Lemma match_arg_Prod_correct {t1 t2} (a:arg _ (Prod t1 t2)) (a1:arg _ t1) (a2:arg _ t2) :
      match_arg_Prod a = (a1, a2) <-> a = (Pair a1 a2).
    Proof.
      pose proof (match_arg_Prod_correct_helper a) as H; simpl in H; rewrite H; reflexivity.
    Qed.

    Lemma Pair_eq t0 t1 x0 x1 x0' x1' : @Pair var t0 x0 t1 x1 = @Pair var t0 x0' t1 x1' <-> (x0, x1) = (x0', x1').
    Proof.
      split; intro H; try congruence.
      apply (f_equal match_arg_Prod) in H; assumption.
    Qed.
  End match_arg.

  Fixpoint uninterp_arg {t} {struct t} : interp_flat_type t -> @arg interp_type t
    := match t return interp_flat_type t -> @arg interp_type t with
       | Prod t1 t2 => fun x => let (x1, x2) := x in
                                Pair (@uninterp_arg t1 x1) (@uninterp_arg t2 x2)
       | TW => @Var interp_type _
       | Tbool => @Var interp_type _
       | TZ => Const
       end.

  Lemma interp_arg_uninterp_arg : forall t (a:interp_flat_type t), interp_arg (uninterp_arg a) = a.
  Proof.
    induction t; simpl; intros; try reflexivity;
      repeat break_match; subst; simpl; intuition try congruence.
  Qed.

  Lemma interp_simple_arg_uninterp_arg : forall (t : flat_type) (a:interp_type t), @interp_simple_arg t (@uninterp_arg t a) = a.
  Proof.
    apply interp_arg_uninterp_arg.
  Qed.

  Lemma interp_under_lets {t: flat_type} {tC: type}
        (e: @expr _ t)
        (C: @arg _ t -> @expr _ tC)
        (C_Proper : forall a1 a2, interp_arg a1 = interp_arg a2 ->
              interp (C a1) = interp (C a2)) :
    pointwise_eq_interp (@interp tC (under_lets e C)) (@interp tC (C (@uninterp_arg t (interp e)))).
  Proof.
    intros; apply (@under_lets_correct t);
    [ assumption
    | rewrite interp_simple_arg_uninterp_arg; reflexivity ].
  Qed.

  Lemma interp_under_lets_flat {t: flat_type} {tC: flat_type}
        (e: @expr _ t)
        (C: @arg _ t -> @expr _ tC)
        (C_Proper : forall a1 a2, interp_arg a1 = interp_arg a2 ->
              interp (C a1) = interp (C a2)) :
    @interp tC (under_lets e C)  = @interp tC (C (@uninterp_arg t (interp e))).
  Proof.
    apply (@interp_under_lets t tC); assumption.
  Qed.

  Lemma interp_under_lets_pointwise {t: flat_type} {tC: type}
        (e: @expr _ t)
        (C: @arg _ t -> @expr _ tC)
        (C_Proper : forall a1 a2, pointwise_eq_interp (interp_arg a1) (interp_arg a2) ->
              pointwise_eq_interp (interp (C a1)) (interp (C a2))) :
    pointwise_eq_interp (@interp tC (under_lets e C)) (@interp tC (C (@uninterp_arg t (interp e)))).
  Proof.
    intros; apply (@under_lets_correct_pointwise t);
    [ assumption
    | rewrite interp_simple_arg_uninterp_arg; reflexivity ].
  Qed.

  Lemma interp_under_lets_no_abs_pointwise {t: flat_type} {tC: type}
        (e: @expr _ t)
        (C: expr_or_arg (Tflat t) -> @expr _ tC)
        (C_Proper : forall a1 a2, pointwise_eq_interp (interp_expr_or_arg (t:=t) a1) (interp_expr_or_arg (t:=t) a2) ->
              pointwise_eq_interp (interp (C a1)) (interp (C a2))) :
    pointwise_eq_interp (@interp tC (under_lets_no_abs e C)) (@interp tC (C (@uninterp_arg t (interp e)))).
  Proof.
    intros; apply (@under_lets_no_abs_correct_pointwise t); simpl;
    [ assumption
    | rewrite interp_arg_uninterp_arg; reflexivity ].
  Qed.

  Section wf.
    Context {var1 var2 : vartype -> Type}.

    Local Notation "x ≡ y" := (existT _ _ (x, y)).

    Inductive wf_arg : list (sigT (fun t => var1 t * var2 t))%type -> forall {t}, @arg var1 t -> @arg var2 t -> Prop :=
    | WfConst : forall G t n, wf_arg G (Const (t := t) n) (Const n)
    | WfSpZConst : forall G n, wf_arg G (SpZConst n) (SpZConst n)
    | WfVar : forall G (t : vartype) x x', In (x ≡ x') G -> @wf_arg G t (Var x) (Var x')
    | WfPair : forall G {t1} {t2} (e1: @arg var1 t1) (e2: @arg var1 t2)
                      (e1': @arg var2 t1) (e2': @arg var2 t2),
        wf_arg G e1 e1'
        -> wf_arg G e2 e2'
        -> wf_arg G (Pair e1 e2) (Pair e1' e2').

    Inductive wf : list (sigT (fun t => var1 t * var2 t))%type -> forall {t}, @expr var1 t -> @expr var2 t -> Prop :=
    | WfLetUnop : forall G {t1} (op : nop 1 1 t1 _) (e1:@arg var1 t1) (e1':@arg var2 t1)
                         tC b b',
        wf_arg G e1 e1'
        -> (forall x1 x2, wf ((x1 ≡ x2) :: G) (b x1) (b' x2))
        -> wf G (LetUnop (tC := tC) op e1 b) (LetUnop (tC := tC) op e1' b')
    | WfLetBinop : forall G {t10 t11} (op : nop 2 1 (t10, t11) _)
                       (e10:@arg var1 t10) (e11:@arg var1 t11)
                       (e10':@arg var2 t10) (e11':@arg var2 t11)
                       tC b b',
        wf_arg G e10 e10'
        -> wf_arg G e11 e11'
        -> (forall x1 x2, wf ((x1 ≡ x2) :: G) (b x1) (b' x2))
        -> wf G (LetBinop (tC := tC) op e10 e11 b) (LetBinop (tC := tC) op e10' e11' b')
    | WfLetTrinop : forall G {t10 t11 t12} (op : nop 3 1 (t10, t11, t12) _)
                       (e10:@arg var1 t10) (e11:@arg var1 t11) (e12:@arg var1 t12)
                       (e10':@arg var2 t10) (e11':@arg var2 t11) (e12':@arg var2 t12)
                       tC b b',
        wf_arg G e10 e10'
        -> wf_arg G e11 e11'
        -> wf_arg G e12 e12'
        -> (forall x1 x2, wf ((x1 ≡ x2) :: G) (b x1) (b' x2))
        -> wf G (LetTrinop (tC := tC) op e10 e11 e12 b) (LetTrinop (tC := tC) op e10' e11' e12' b')
    | WfLetTrinop2Ret : forall G {t10 t11 t12} (op : nop 3 2 (t10, t11, t12) _)
                       (e10:@arg var1 t10) (e11:@arg var1 t11) (e12:@arg var1 t12)
                       (e10':@arg var2 t10) (e11':@arg var2 t11) (e12':@arg var2 t12)
                       tC b b',
        wf_arg G e10 e10'
        -> wf_arg G e11 e11'
        -> wf_arg G e12 e12'
        -> (forall x10 x11 x20 x21, wf ((x11 ≡ x21) :: (x10 ≡ x20) :: G) (b x10 x11) (b' x20 x21))
        -> wf G (LetTrinop2Ret (tC := tC) op e10 e11 e12 b) (LetTrinop2Ret (tC := tC) op e10' e11' e12' b')
    | WfAbs : forall G t1 t2 e e',
        (forall x1 x2, wf ((x1 ≡ x2) :: G) (e x1) (e' x2))
        -> wf G (@Abs _ t1 t2 e) (Abs e')
    | WfReturn : forall G t x x', wf_arg G x x' -> wf G (Return (t := t) x) (Return x').

  End wf.

  Definition Wf {t} (E : @Expr t) := forall var1 var2, wf nil (E var1) (E var2).

End Output.

Section compile.
  Context {ivar : vartype -> Type}.
  Context {ovar : vartype -> Type}.

  Fixpoint reify_interped {t} : interp_flat_type t -> @Output.expr ovar t
    := match t return interp_type t -> @Output.expr ovar t with
       | Prod t0 t1
         => fun x0x1
            => @Output.under_lets
                 _ _ (@reify_interped t0 (fst x0x1)) _
                 (fun x0
                  => @Output.under_lets
                       _ _ (@reify_interped t1 (snd x0x1)) _
                       (fun x1
                        => Output.Return (Output.Pair x0 x1)))
       | TZ => fun n => Output.Return (Output.Const n)
       | TW => fun n => Output.Return (Output.Const n)
       | Tbool => fun n => Output.Return (Output.Const n)
       end.

  Fixpoint compile {t} (e:@Input.expr (@Output.arg ovar) t) : @Output.expr ovar t
    := match e in @Input.expr _ t return @Output.expr ovar t with
           | Input.Const _ n => reify_interped n
           | Input.SpZConst n => Output.Return (Output.SpZConst n)
           | Input.Var _ n => Output.Return n
           | Input.Unop _ TW op a =>
             Output.under_lets (@compile _ a) (fun arg1 =>
                Output.LetUnop op arg1 (fun v => Output.Return (Output.Var v)))
           | Input.Unop _ _ op a => match op with OPldi => fun x => x end (* whee small inversion magic *)
           | Input.Binop _ _ TW op a b =>
             Output.under_lets (@compile _ a) (fun arg1 =>
             Output.under_lets (@compile _ b) (fun arg2 =>
                Output.LetBinop op arg1 arg2 (fun v => Output.Return (Output.Var v))))
           | Input.Binop _ _ _ op a b => match op with OPldi => fun x => x end (* whee small inversion magic *)
           | Input.Trinop _ _ _ TW op a b c =>
             Output.under_lets (@compile _ a) (fun arg1 =>
             Output.under_lets (@compile _ b) (fun arg2 =>
             Output.under_lets (@compile _ c) (fun arg3 =>
                Output.LetTrinop op arg1 arg2 arg3 (fun v => Output.Return (Output.Var v)))))
           | Input.Trinop _ _ _ _ op a b c => match op with OPldi => fun x => x end (* whee small inversion magic *)
           | Input.Trinop2Ret _ _ _ (Tbool, TW) op a b c =>
             Output.under_lets (@compile _ a) (fun arg1 =>
             Output.under_lets (@compile _ b) (fun arg2 =>
             Output.under_lets (@compile _ c) (fun arg3 =>
                Output.LetTrinop2Ret op arg1 arg2 arg3 (fun v0 v1 => Output.Return (Output.Pair (Output.Var v0) (Output.Var v1))))))
           | Input.Trinop2Ret _ _ _ _ op a b c => match op with OPldi => fun x => x end (* whee small inversion magic *)
    | Input.Let _ ex _ eC =>
       Output.under_lets (@compile _ ex) (fun arg => @compile _ (eC arg))
    | Input.Pair _ e1 _ e2 =>
       Output.under_lets (@compile _ e1) (fun arg1 =>
          Output.under_lets (@compile _ e2) (fun arg2 =>
             Output.Return (Output.Pair arg1 arg2)))
    | Input.MatchPair _ _ ep _ eC =>
        Output.under_lets (@compile _ ep) (fun arg =>
          let (a1, a2) := Output.match_arg_Prod arg in @compile _ (eC a1 a2))
    | Input.Abs _ _ f => Output.Abs (fun x => @compile _ (f (Output.Var x)))
           end.
  End compile.

Definition Compile {t} (e:Input.Expr t) : Output.Expr t := fun var =>
  compile (e (@Output.arg var)).

Lemma interp_reify_interped t n
  : Output.interp (t := Tflat t) (reify_interped n) = n.
Proof.
  induction t; simpl.
  { repeat break_match; reflexivity. }
  { repeat first [ reflexivity
                 | rewrite !Output.interp_under_lets
                 | rewrite !Output.interp_arg_uninterp_arg
                 | rewrite <- surjective_pairing
                 | intro
                 | progress simpl in *
                 | rewrite_hyp !* ]. }
Qed.

Lemma compile_correct {t} e1 e2 G (wf:Input.wf G e1 e2) :
  List.Forall (fun v => let 'existT _ (x, a) := v in Output.interp_arg a = x) G ->
    Output.pointwise_eq_interp (t := t) (Output.interp (compile e2)) (Input.interp e1).
Proof.
  induction wf;
    repeat repeat match goal with
           | [ |- ?R ?x ?x ] => reflexivity
    | [HIn:In ?x ?l, HForall:Forall _ ?l |- _ ] =>
      (pose proof (proj1 (Forall_forall _ _) HForall _ HIn); clear HIn)
    | [ H : Output.match_arg_Prod _ = (_, _) |- _ ] =>
      apply Output.match_arg_Prod_correct in H
    | [ H : Output.Pair _ _ = Output.Pair _ _ |- _ ] =>
      apply Output.Pair_eq in H
    | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
    | _ => progress intros
    | _ => progress simpl in *
    | _ => progress subst
    | _ => progress specialize_by assumption
    | _ => progress break_match
    | _ => rewrite !Output.interp_under_lets_pointwise
    | _ => rewrite !Output.interp_under_lets_flat
    | _ => rewrite !Output.interp_under_lets
    | _ => rewrite !interp_reify_interped
    | _ => rewrite !Output.interp_arg_uninterp_arg
    | _ => rewrite <- !surjective_pairing
    | _ => progress erewrite_hyp !*
    | _ => apply Forall_cons
    | [ |- context[match ?op with OPldi => _ | _ => _ end] ]
      => solve [ exfalso; refine (match op with OPldi => idProp end) ]
    | _ => solve [intuition (congruence || eauto)]
    | [ H : _ |- Output.pointwise_eq_interp _ _ ] => apply H
    end.
Qed.

Lemma Compile_correct {t} (E:Input.Expr t) (WfE:Input.Wf E) :
  Output.pointwise_eq_interp (Output.Interp (Compile E)) (Input.Interp E).
Proof. eapply compile_correct; eauto. Qed.

Section symbolic.
  Local Set Boolean Equality Schemes.
  Local Set Decidable Equality Schemes.
  (** Holds decidably-equal versions of raw expressions, for lookup. *)
  Inductive sop : Set :=
    SOPldi | SOPshrd | SOPshl | SOPshr | SOPmkl | SOPadc | SOPsubc | SOPmulhwll | SOPmulhwhl | SOPmulhwhh | SOPselc | SOPaddm.
  Inductive SymbolicExpr : Set :=
  | SConstZ : Z -> SymbolicExpr
  | SSpZConst : SpecialZConst -> SymbolicExpr
  | SConstBool : bool -> SymbolicExpr
  | SConstW : nat -> SymbolicExpr
  | SVar : vartype -> nat -> SymbolicExpr
  | SPair : SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  | SUnOp : sop -> SymbolicExpr -> SymbolicExpr
  | SBinOp : sop -> SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  | STrinOp : sop -> SymbolicExpr -> SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  | STrinOp2Ret : sop -> SymbolicExpr -> SymbolicExpr -> SymbolicExpr -> SymbolicExpr.
End symbolic.

Section CSE.
  Context {var : vartype -> Type}.
  Let svar t := (var t * SymbolicExpr)%type.
  Let mapping := (list (svar TW) * list (svar Tbool))%type.

  Fixpoint lookup' {t} (sv : SymbolicExpr) (xs : list (svar t)) {struct xs} : option (var t) :=
    match xs with
    | nil => None
    | (x, sv') :: xs' =>
      if SymbolicExpr_beq sv' sv
      then Some x
      else lookup' sv xs'
    end.
  Definition lookup t (sv : SymbolicExpr) (xs : mapping) : option (var t) :=
    match t with
    | TW => lookup' sv (fst xs)
    | Tbool => lookup' sv (snd xs)
    end.
  Definition mapping_nth_error (xs : mapping) t n : option (svar t) :=
    match t with
    | TW => nth_error (fst xs) n
    | Tbool => nth_error (snd xs) n
    end.
  Definition symbolicify_var {t : vartype} (v : var t) (xs : mapping) : SymbolicExpr :=
    SVar t (match t with
            | TW => length (fst xs)
            | Tbool => length (snd xs)
            end).
  Definition add_mapping {t} (v : var t) (sv : SymbolicExpr) (xs : mapping) : mapping :=
    match t return var t -> mapping with
    | TW => fun v => ((v, sv) :: fst xs, snd xs)
    | Tbool => fun v => (fst xs, (v, sv) :: snd xs)
    end v.
  Definition sop_eval_dep (op : sop)
    := match op return match op with SOPldi => _ | _ => _ end with
       | SOPldi => OPldi
       | SOPshrd => OPshrd
       | SOPshl => OPshl
       | SOPshr => OPshr
       | SOPmkl => OPmkl
       | SOPadc => OPadc
       | SOPsubc => OPsubc
       | SOPmulhwll => OPmulhwll
       | SOPmulhwhl => OPmulhwhl
       | SOPmulhwhh => OPmulhwhh
       | SOPselc => OPselc
       | SOPaddm => OPaddm
       end.
  Definition sop_eval nret (op : sop) (t : tuple flat_type nret) : option (sigT (fun nargs : nat => sigT (fun args : tuple flat_type nargs => nop nargs nret args t)))
    := match nret return forall t : tuple flat_type nret, option (sigT (fun nargs : nat => sigT (fun args : tuple flat_type nargs => nop nargs nret args t))) with
       | 1%nat => fun t => match op, t with
                     | SOPldi as op, TW
                     | SOPshrd as op, TW
                     | SOPshr as op, TW
                     | SOPshl as op, TW
                     | SOPmkl as op, TW
                     | SOPmulhwll as op, TW
                     | SOPmulhwhl as op, TW
                     | SOPmulhwhh as op, TW
                     | SOPselc as op, TW
                     | SOPaddm as op, TW
                       => Some (existT _ _ (existT _ _ (sop_eval_dep op)))
                     | _, _ => None
                     end
       | 2%nat => fun t => match op, t with
                     | SOPadc as op, (Tbool, TW)
                     | SOPsubc as op, (Tbool, TW)
                       => Some (existT _ _ (existT _ _ (sop_eval_dep op)))
                     | _, _ => None
                     end
       | _ => fun _ => None
       end t.
  Fixpoint symbolic_preeval {t} (xs : mapping) (e : SymbolicExpr) : option (@Output.expr var t)
    := match e, t return option (@Output.expr var t) with
           | SConstZ v, TZ as t
           | SConstBool v, Tbool as t
             => Some (Output.Return (Output.Const (t := t) v))
           | SConstZ _, _ => None
           | SConstBool _, _ => None
           | SSpZConst v, TZ => Some (Output.Return (Output.SpZConst v))
           | SSpZConst _, _ => None
           | SConstW n, TW as t => option_map (fun x => Output.Return (Output.Var (fst x)))
                                             (mapping_nth_error xs t n)
           | SConstW _, _ => None
           | SVar Tbool n, Tbool as t
           | SVar TW n, TW as t
             => option_map (fun x => Output.Return (Output.Var (fst x)))
                          (mapping_nth_error xs t n)
           | SVar _ _, _ => None
           | SPair x y, Prod tx ty
             => match @symbolic_preeval tx xs x, @symbolic_preeval ty xs y with
               | Some x', Some y' => Some (Output.under_lets x' (fun x0 => Output.under_lets y' (fun y0 => Output.Return (Output.Pair x0 y0))))
               | _, _ => None
               end
           | SPair _ _, _ => None
           | SUnOp op x0, TW as t
             => match sop_eval 1 op t with
               | Some (existT 1%nat (existT x0t opv))
                 => option_map
                     (fun x0' : Output.expr x0t
                      => Output.under_lets
                           x0' (fun x0' => Output.LetUnop
                                             opv x0'
                                             (fun v => Output.Return (Output.Var v))))
                     (@symbolic_preeval x0t xs x0)
               | _ => None
               end
           | SUnOp _ _, _ => None
           | SBinOp op x0 x1, TW as t
             => match sop_eval 1 op t with
               | Some (existT 2%nat (existT (x0t, x1t) opv))
                 => match @symbolic_preeval x0t xs x0, @symbolic_preeval x1t xs x1 with
                   | Some x0', Some x1'
                     => Some
                         (Output.under_lets
                            x0' (fun x0' =>
                                   Output.under_lets
                                     x1' (fun x1' =>
                                            Output.LetBinop
                                              opv x0' x1'
                                              (fun v => Output.Return (Output.Var v)))))
                   | _, _ => None
                   end
               | _ => None
               end
           | SBinOp _ _ _, _ => None
           | STrinOp op x0 x1 x2, TW as t
             => match sop_eval 1 op t with
               | Some (existT 3%nat (existT (x0t, x1t, x2t) opv))
                 => match @symbolic_preeval x0t xs x0, @symbolic_preeval x1t xs x1, @symbolic_preeval x2t xs x2 with
                   | Some x0', Some x1', Some x2'
                     => Some
                         (Output.under_lets
                            x0' (fun x0' =>
                                   Output.under_lets
                                     x1' (fun x1' =>
                                            Output.under_lets
                                              x2' (fun x2' => Output.LetTrinop
                                                             opv x0' x1' x2'
                                                             (fun v => Output.Return (Output.Var v))))))
                   | _, _, _ => None
                   end
               | _ => None
               end
           | STrinOp _ _ _ _, _ => None
           | STrinOp2Ret op x0 x1 x2, (Prod Tbool TW) as t
             => match sop_eval 2 op (Tbool:flat_type, TW:flat_type) with
               | Some (existT 3%nat (existT (x0t, x1t, x2t) opv))
                 => match @symbolic_preeval x0t xs x0, @symbolic_preeval x1t xs x1, @symbolic_preeval x2t xs x2 with
                   | Some x0', Some x1', Some x2'
                     => Some
                         (Output.under_lets
                            x0' (fun x0' =>
                                   Output.under_lets
                                     x1' (fun x1' =>
                                            Output.under_lets
                                              x2' (fun x2' => Output.LetTrinop2Ret
                                                             opv x0' x1' x2'
                                                             (fun c v => Output.Return (Output.Pair (Output.Var c) (Output.Var v)))))))
                   | _, _, _ => None
                   end
               | _ => None
               end
           | STrinOp2Ret _ _ _ _, _ => None
       end.

  Fixpoint cseArg {t} (v : @Output.arg svar t) (xs : mapping) {struct v}
    : @Output.arg var t * option SymbolicExpr
    := match v in Output.arg t return Output.arg t * option SymbolicExpr with
       | Output.Const Tbool v'
         => let sv := SConstBool v' in
           (match lookup Tbool sv xs with
            | Some val => Output.Var val
            | None => Output.Const v'
            end,
            Some sv)
       | Output.Const TZ v'
         => (Output.Const v', Some (SConstZ v'))
       | Output.SpZConst v'
         => (Output.SpZConst v', Some (SSpZConst v'))
       | Output.Const _ v' => (Output.Const v', None)
       | Output.Var t v'
         => (Output.Var (match lookup t (snd v') xs with
                        | Some val => val
                        | None => fst v'
                        end),
            Some (snd v'))
       | Output.Pair _ v0 _ v1
         => let '(v0v, v0s) := eta (@cseArg _ v0 xs) in
           let '(v1v, v1s) := eta (@cseArg _ v1 xs) in
           (Output.Pair v0v v1v,
            match v0s, v1s with
            | Some v0', Some v1' => Some (SPair v0' v1')
            | _, _ => None
            end)
       end.
  Definition cseOp {narg nret t1 t2} (op : @nop narg nret t1 t2) : sop
    := match op with
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

  Definition cseExprHelper1
             (cseExpr : forall t (v : @Output.expr svar t) (xs : mapping), @Output.expr var t)
             (xs : mapping)
             {tC}
             (f : svar TW -> @Output.expr svar tC)
             (sv : option SymbolicExpr)
             (default_head : (var TW -> @Output.expr var tC) -> @Output.expr var tC)
    : @Output.expr var tC
    := match option_map (fun sv' => (sv', lookup _ sv' xs)) sv with
       | Some (sv', Some v') => @cseExpr _ (f (v', sv')) xs
       | Some (sv', None)    => default_head (fun v => @cseExpr _ (f (v, sv')) (add_mapping v sv' xs))
       | None                => default_head (fun v => let sv' := symbolicify_var v xs in
                                                       @cseExpr _ (f (v, sv')) (add_mapping v sv' xs))
       end.
  Definition cseExprHelper2
             (cseExpr : forall t (v : @Output.expr svar t) (xs : mapping), @Output.expr var t)
             (xs : mapping)
             {tC}
             (f : svar Tbool -> svar TW -> @Output.expr svar tC)
             (sv : option SymbolicExpr)
             (default_head : (var Tbool -> var TW -> @Output.expr var tC) -> @Output.expr var tC)
    : @Output.expr var tC
    := match option_map (fun sv' => (sv', lookup Tbool sv' xs, lookup TW sv' xs)) sv with
       | Some (sv', Some vb', Some vw')
         => @cseExpr _ (f (vb', sv') (vw', sv')) xs
       | Some (sv', _, _)
         => default_head (fun vb vw => @cseExpr _ (f (vb, sv') (vw, sv'))
                                                (add_mapping vw sv' (add_mapping vb sv' xs)))
       | None
         => default_head (fun vb vw => let svb' := symbolicify_var vb xs in
                                       let svw' := symbolicify_var vw xs in
                                       @cseExpr _ (f (vb, svb') (vw, svw'))
                                                (add_mapping vw svw' (add_mapping vb svb' xs)))
       end.
  Definition cseExpr_step
             (cseExpr : forall {t} (v : @Output.expr svar t) (xs : mapping), @Output.expr var t)
             {t} (v : @Output.expr svar t) (xs : mapping)
    : @Output.expr var t
    := match v in Output.expr t return Output.expr t with
       | Output.LetUnop _ op x0 _ f
         => let sop := cseOp op in
            let '(x0v, x0s) := eta (cseArg x0 xs) in
            let sv := match x0s with
                      | Some x0' => Some (SUnOp sop x0')
                      | _ => None
                      end in
            let default_head := Output.LetUnop op x0v in
            cseExprHelper1 (@cseExpr) xs f sv default_head
       | Output.LetBinop _ _ op x0 x1 _ f
         => let sop := cseOp op in
            let '(x0v, x0s) := eta (cseArg x0 xs) in
            let '(x1v, x1s) := eta (cseArg x1 xs) in
            let sv := match x0s, x1s with
                      | Some x0', Some x1' => Some (SBinOp sop x0' x1')
                      | _, _ => None
                      end in
            let default_head := Output.LetBinop op x0v x1v in
            cseExprHelper1 (@cseExpr) xs f sv default_head
       | Output.LetTrinop _ _ _ op x0 x1 x2 _ f
         => let sop := cseOp op in
            let '(x0v, x0s) := eta (cseArg x0 xs) in
            let '(x1v, x1s) := eta (cseArg x1 xs) in
            let '(x2v, x2s) := eta (cseArg x2 xs) in
            let sv := match x0s, x1s, x2s with
                      | Some x0', Some x1', Some x2' => Some (STrinOp sop x0' x1' x2')
                      | _, _, _ => None
                      end in
            let default_head := Output.LetTrinop op x0v x1v x2v in
            cseExprHelper1 (@cseExpr) xs f sv default_head
       | Output.LetTrinop2Ret _ _ _ op x0 x1 x2 _ f
         => let sop := cseOp op in
            let '(x0v, x0s) := eta (cseArg x0 xs) in
            let '(x1v, x1s) := eta (cseArg x1 xs) in
            let '(x2v, x2s) := eta (cseArg x2 xs) in
            let sv := match x0s, x1s, x2s with
                      | Some x0', Some x1', Some x2' => Some (STrinOp2Ret sop x0' x1' x2')
                      | _, _, _ => None
                      end in
            let default_head := Output.LetTrinop2Ret op x0v x1v x2v in
            cseExprHelper2 (@cseExpr) xs f sv default_head
       | Output.Return _ x => Output.Return (fst (cseArg x xs))
       | Output.Abs _ _ f => Output.Abs (fun x => let sx := symbolicify_var x xs in
                                                  @cseExpr _ (f (x, sx)) (add_mapping x sx xs))
       end.
End CSE.
Definition symbolic_eval {t} xs sv := option_map Output.interp (@symbolic_preeval _ t xs sv).
Fixpoint cseExpr' {var t} v xs := @cseExpr_step var (@cseExpr' var) t v xs.

Fixpoint under_spzconst {var} (ls : list SpecialZConst) {T} (v : Output.expr (var:=var) T) : Output.expr T :=
  match ls with
  | nil => v
  | cons x xs => Output.LetUnop OPldi (Output.SpZConst x) (fun x => @under_spzconst var xs T v)
  end.

Fixpoint cseExpr {var}
         {t} (v : @Output.expr _ t) xs
  := match v in Output.expr t return @Output.expr var t with
     | Output.Abs _ _ f => Output.Abs (fun x => let sx := symbolicify_var x xs in
                                                @cseExpr _ _ (f (x, sx)) (add_mapping x sx xs))
     | v => @cseExpr'
              var _
              (Output.LetUnop OPldi (Output.Const (0:interp_type TZ)) (fun RegZero =>
               under_spzconst all_SpecialZConst v))
              xs
     end.

Definition CSE {t} (e:Output.Expr t) : Output.Expr t := fun var =>
  @cseExpr var t (e _) (nil, nil).

Local Ltac specialize_vartype :=
  repeat match goal with
         | [ H : forall x : vartype, _ |- _ ]
           => pose proof (H Tbool); pose proof (H TW); clear H
         end.

Lemma lookup_correct
      (var := interp_type)
      (svar := fun t => (var t * SymbolicExpr)%type)
      (mapping := (list (svar TW) * list (svar Tbool))%type)
  : forall sv vs (G : list (sigT (fun t : vartype => (interp_type t * (interp_type t * SymbolicExpr))%type))) (xs : mapping),
    (forall t x1 sv x2, In (existT _ t (x1, (x2, sv))) G -> x1 = x2)
    -> (forall t x1 sv x2,
           In (existT _ t (x1, (x2, sv))) G -> symbolic_eval vs sv = Some x1)
    -> (forall t x sv, lookup (var:=var) t sv xs = Some x -> In (existT _ t (x, (x, sv))) G)
    -> forall t, match lookup (var:=var) t sv xs with
                 | Some x' => symbolic_eval vs sv = Some x' /\ In (existT _ t (x', (x', sv))) G
                 | None => True
                 end.
Proof.
  induction xs;
    repeat first [ congruence
                 | solve [ trivial ]
                 | progress intros
                 | progress subst
                 | progress simpl in *
                 | progress break_match
                 | progress inversion_option
                 | progress specialize_vartype
                 | solve [ eauto ] ].
Qed.

(*
Local Ltac SymbolicExpr_beq_to_eq :=
  repeat match goal with
         | [ H : SymbolicExpr_beq _ _ = true |- _ ] => apply internal_SymbolicExpr_dec_bl in H
         | [ H : context[SymbolicExpr_beq ?x ?x] |- _ ]
           => rewrite (@internal_SymbolicExpr_dec_lb x x eq_refl) in H
         end.
Lemma wf_good_lookup t G s xs b
      (H : wf_context_mapping_good G xs)
  : lookup (var:=interp_type) t s xs = Some b
    -> option_map Output.interp (symbolic_eval xs s) = Some b.
Proof.
  destruct xs as [ls0 ls1], t; simpl in *;
    first [ revert dependent ls0; induction ls1 as [|?? IHxs]
          | revert dependent ls1; induction ls0 as [|?? IHxs] ];
    repeat match goal with
           | _ => congruence
           | _ => progress simpl
           | _ => progress break_match
           | _ => progress intros
           | _ => progress congruence_option
           | _ => progress SymbolicExpr_beq_to_eq
           | _ => progress subst
           end.
Admitted.

Local Ltac apply_lookup_good :=
  repeat match goal with
         | [ H : lookup' _ _ = Some _ |- _ ]
           => first [ eapply (@wf_good_lookup Tbool) in H; [ | eassumption ]
                    | eapply (@wf_good_lookup TW) in H; [ | eassumption ] ]
         end.

Lemma wf_context_mapping_good_In_sym_eval_eq t G xs x b x'
      (H : wf_context_mapping_good G xs)
      (HIn : In (existT _ t (x, x')) G)
  : option_map Output.interp (symbolic_eval (t := t) xs (snd x')) = Some b
    -> b = x.
Proof.
Admitted.

Lemma wf_good_lookup_None_In t G xs x x'
      (H : wf_context_mapping_good G xs)
      (HIn : In (existT _ t (x, x')) G)
  : lookup (var:=interp_type) t (snd x') xs = None
    -> fst x' = x.
Proof.
  destruct xs as [ls0 ls1], t; simpl in *;
    first [ revert dependent ls0; induction ls1 as [|?? IHxs]
          | revert dependent ls1; induction ls0 as [|?? IHxs] ];
    repeat match goal with
           | _ => congruence
           | _ => progress simpl
           | _ => progress break_match
           | _ => progress intros
           | _ => progress congruence_option
           | _ => progress SymbolicExpr_beq_to_eq
           | _ => progress subst
           end.
Admitted.

(*Local Ltac use_wf_context_mapping_good_In_sym_eval_eq
  := repeat match goal with
            | [ H : option_map Output.interp (symbolic_eval (t := Tflat (Tconst (Tvar ?t))) ?xs (snd ?x')) = Some ?b |- _]
              => eapply (@wf_context_mapping_good_In_sym_eval_eq t _ xs _ b x') in H; [ | eassumption | eassumption ]
            end.

Lemma wf_to_interp_arg t G x x' xs
      (wf : Output.wf_arg G x x')
      (Hgood : wf_context_mapping_good G xs)
  : Output.interp_arg (fst (cseArg x' xs)) = Output.interp_arg (t := t) x.
Proof.
  revert dependent xs; induction wf;
    repeat match goal with
           | _ => reflexivity
           | _ => progress intros
           | _ => progress subst
           | _ => progress simpl in *
           | _ => progress break_match
           | _ => progress congruence_option
           | _ => progress apply_lookup_good
           | _ => progress use_wf_context_mapping_good_In_sym_eval_eq
           | _ => progress unfold cseExprHelper1, cseExprHelper2 in *
           end.
lazymatch goal with
            | [ H : option_map Output.interp (symbolic_eval (t := Tflat (Tconst (Tvar ?t))) ?xs (snd ?x')) = Some ?b |- _]
              => eapply (@wf_context_mapping_good_In_sym_eval_eq t _ xs _ b x') in H
end.
eapply wf_context_mapping_good_In_sym_eval_eq in Heqo.
eappply

Lemma wf_context_mapping_good_unop G t (op : nop 1 1 t TW) xs s w
      (e : @Output.arg interp_type t)
      (e' : @Output.arg (fun t' => interp_type t' * SymbolicExpr)%type t)
      (H : wf_context_mapping_good G xs)
      (Heq : snd (cseArg (var:=interp_type) e' xs) = Some s)
      (Hlookup : lookup (var:=interp_type) TW (SUnOp (cseOp op) s) xs = Some w)
      (wf : Output.wf_arg G e e')
  : wf_context_mapping_good
      (existT _ _ (interp_nop op (Output.interp_arg e), (w, SUnOp (cseOp op) s)) :: G) xs.
Proof.
  revert dependent s.
  revert dependent w.
  revert H.
  induction wf;
    repeat match goal with
           | _ => progress intros
           | _ => progress subst
           | _ => progress simpl in *
           | _ => progress break_match
           | _ => progress congruence_option
           | _ => progress unfold cseExprHelper1, cseExprHelper2 in *
           end.
Admitted.
(*Lemma wf_context_mapping_good_unop' G t (op : nop 1 1 t TW) xs s w
      (e : @Output.arg interp_type t)
      (e' : @Output.arg (fun t' => interp_type t' * SymbolicExpr)%type t)
      (H : wf_context_mapping_good G xs)
      (Heq : snd (cseArg (var:=interp_type) e' xs) = Some s)
      (Hlookup : lookup (var:=interp_type) TW (SUnOp (cseOp op) s) xs = None)
      (wf : Output.wf_arg G e e')
  : wf_context_mapping_good
      (existT _ _ (interp_nop op (Output.interp_arg e), (w, SUnOp (cseOp op) s)) :: G) xs.
Proof.
  wf_context_mapping_good
    (existT
       (fun t : vartype =>
        (match t with
         | Tbool => bool
         | TW => fancy_machine.W
         end * (match t with
                | Tbool => bool
                | TW => fancy_machine.W
                end * SymbolicExpr))%type) TW
       (interp_nop op (Output.interp_arg e1),
       (interp_nop op (Output.interp_arg (fst (cseArg e1' xs))), SUnOp (cseOp op) s)) :: G)
    ((interp_nop op (Output.interp_arg (fst (cseArg e1' xs))), SUnOp (cseOp op) s) :: fst xs, snd xs)
*)*)*)

Definition wf_context_mapping_good
           (var := interp_type)
           (svar := fun t => (var t * SymbolicExpr)%type)
           (mapping := (list (svar TW) * list (svar Tbool))%type)
  : list (sigT (fun t : vartype => (interp_type t * (interp_type t * SymbolicExpr))%type))
    -> mapping
    -> Prop
  := fun G xs
     => (forall t x1 sv x2, In (existT _ t (x1, (x2, sv))) G -> x1 = x2)
        /\ (forall t x1 sv x2,
               In (existT _ t (x1, (x2, sv))) G -> symbolic_eval xs sv = Some x1)
        /\ (forall t x sv, lookup (var:=var) t sv xs = Some x -> In (existT _ t (x, (x, sv))) G).

(*Lemma wf_context_mapping_good_cons g G xs
  : wf_context_mapping_good (g :: G) xs
    <-> (let '(x1, (x2, sv)) := eta3' (projT2 g) in
         x1 = x2
         /\ symbolic_eval xs sv = Some x1
         /\ ((forall t, lookup (var:=interp_type) t sv xs = None) \/ In g G)
         /\ wf_context_mapping_good G xs).
Proof.
  destruct g as [? [? [? ?] ] ]; simpl.
  unfold wf_context_mapping_good; simpl;
    repeat intuition (subst || inversion_sigma || inversion_prod || simpl in * || eauto || specialize_vartype).
  destruct x.
  repeat match goal with
         | [ x : _, H' : forall y, _ |- _ ] => unique pose proof (H' x)
         end.
  repeat match goal with
         | [ H : None = Some _ -> _ |- _ ] => clear H
         | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
         | [ H : @lookup' ?a ?b ?c ?d = Some _ -> _ |- _ ]
           => destruct (@lookup' a b c d) eqn:?
         end.


         end.
  { repeat match goal with
         | [ H : or _ _ |- _ ] => destruct H
         end.
  specialize_all_ways.
Qed.

Definition wf_context_mapping_good_cons1 g G xs
  := proj2 (wf_context_mapping_good_cons g G xs).

Lemma cseArg_correct {t} (x1 : @Output.arg interp_type t) (x2 : @Output.arg (fun t : vartype => (interp_type t * SymbolicExpr)%type) t) G (wf:Output.wf_arg G x1 x2) xs :
  wf_context_mapping_good G xs ->
    Output.pointwise_eq_interp (t := t) (Output.interp_arg (fst (cseArg x2 xs))) (Output.interp_arg x1).
Proof.
  revert dependent xs; induction wf;
    repeat match goal with
           | _ => congruence
           | _ => progress intros
           | _ => progress subst
           | _ => progress simpl in *
           | _ => progress break_match
           | _ => progress inversion_option
           | _ => progress unfold cseExprHelper1, cseExprHelper2 in *
           end.

  t : flat_type
  x : Output.arg t
  x' : Output.arg t
  H0 : Output.wf_arg G x x'
  xs : list (fancy_machine.W * SymbolicExpr) * list (bool * SymbolicExpr)
  H1 : wf_context_mapping_good G xs
  ============================
  Output.interp_arg (fst (cseArg x' xs)) = Output.interp_arg x


Lemma cse'_correct {t} (e1 : @Output.expr interp_type t) (e2 : @Output.expr (fun t : vartype => (interp_type t * SymbolicExpr)%type) t) G (wf:Output.wf G e1 e2) xs :
  wf_context_mapping_good G xs ->
    Output.pointwise_eq_interp (t := t) (Output.interp (cseExpr' e2 xs)) (Output.interp e1).
Proof.
  revert dependent xs.
  induction wf;
    repeat match goal with
           | _ => congruence
           | _ => progress intros
           | _ => progress subst
           | _ => progress simpl in *
           | _ => progress break_match
           | _ => progress inversion_option
           | _ => progress unfold cseExprHelper1, cseExprHelper2 in *
           end.
  { match goal with
    | [ H : _ |- _ ] => apply H, wf_context_mapping_good_cons1; simpl
    end.
    split; eauto.
    admit. }
  { match goal with
    | [ H : _ |- _ ] => apply H, wf_context_mapping_good_cons1; simpl
    end.
    admit. }
  { match goal with
    | [ H : _ |- _ ] => apply H, wf_context_mapping_good_cons1; simpl
    end.
    admit. }
  { match goal with
    | [ H : _ |- _ ] => apply H, wf_context_mapping_good_cons1; simpl
    end.
    admit. }
  { match goal with
    | [ H : _ |- _ ] => apply H, wf_context_mapping_good_cons1; simpl
    end.
    admit. }
  { match goal with
    | [ H : _ |- _ ] => apply H, wf_context_mapping_good_cons1; simpl
    end.
    admit. }
  { match goal with
    | [ H : _ |- _ ] => apply H, wf_context_mapping_good_cons1; simpl
    end.
    admit. }
  { match goal with
    | [ H : _ |- _ ] => apply H, wf_context_mapping_good_cons1; simpl
    end.
    admit. }
  { match goal with
    | [ H : _ |- _ ] => apply H, wf_context_mapping_good_cons1; simpl
    end.
    admit. }
  { match goal with
    | [ H : _ |- _ ] => apply H, wf_context_mapping_good_cons1; simpl
    end.
    admit. }
  { match goal with
    | [ H : _ |- _ ] => apply H, wf_context_mapping_good_cons1; simpl
    end.
    admit. }
  { match goal with
    | [ H : _ |- _ ] => apply H, wf_context_mapping_good_cons1; simpl
    end.
    admit. }
  { match goal with
    | [ H : _ |- _ ] => apply H, wf_context_mapping_good_cons1; simpl
    end.
    admit. }
  { match goal with
    | [ H : _ |- _ ] => apply H, wf_context_mapping_good_cons1; simpl
    end.
    admit. }
  { match goal with
    | [ H : _ |- _ ] => apply H, wf_context_mapping_good_cons1; simpl
    end.
    admit. }
  { match goal with
    | [ H : _ |- _ ] => apply H, wf_context_mapping_good_cons1; simpl
    end.
    admit. }
  { match goal with
    | [ H : _ |- _ ] => apply H, wf_context_mapping_good_cons1; simpl
    end.
    admit. }
  { match goal with
    | [ H : _ |- _ ] => apply H, wf_context_mapping_good_cons1; simpl
    end.
    admit. }
  { match goal with
    | [ H : _ |- _ ] => apply H, wf_context_mapping_good_cons1; simpl
    end.
    admit. }
  { match goal with
    | [ H : _ |- _ ] => apply H, wf_context_mapping_good_cons1; simpl
    end.
    admit. }
  {
match goal with
    | [ H : _ |- _ ] => apply H, wf_context_mapping_good_cons1; simpl
    end.
    admit. }
  { apply H2, wf_context_mapping_good_cons1; simpl.
    admit. }
  {
apply H2, wf_context_mapping_good_cons1; simpl.
    admit. }
    a
    unfold wf_context_mapping_good in *.
    simpl.
    intros.

    [ apply H2
    | apply H2
    | try apply H2
    | try apply H2
    | try apply H2
    | try apply H2
    | try apply H2
    | try apply H2
    | try apply H2
    | try apply H2
    | try apply H2
    | try apply H2
    | try apply H2
    | try apply H2
    | try apply H2
    | try apply H2
    | try apply H2
    | try apply H2
    | try apply H2
    | ].
  Focus 20.
  {
Set Printing Implicit.
  { apply H2.


pose @symbolic_eval.
cbv beta in *.
Set Printing All.

simpl.
  induction wf;
    repeat match goal with
    | [HIn:In ?x ?l, HForall:Forall _ ?l |- _ ] =>
      (pose proof (proj1 (Forall_forall _ _) HForall _ HIn); clear HIn)
    | [ H : Output.match_arg_Prod _ = (_, _) |- _ ] =>
      apply Output.match_arg_Prod_correct in H
    | [ H : Output.Pair _ _ = Output.Pair _ _ |- _ ] =>
      apply Output.Pair_eq in H
    | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
    | _ => progress intros
    | _ => progress simpl in *
    | _ => progress subst
    | _ => progress specialize_by assumption
    | _ => progress break_match
    | _ => rewrite !Output.interp_under_lets
    | _ => rewrite !Output.interp_arg_uninterp_arg
    | _ => progress erewrite_hyp !*
    | _ => apply Forall_cons
    | _ => solve [intuition (congruence || eauto)]
    end.
Qed.

Lemma Compile_correct {_: Evaluable Z} {t} (E:Input.Expr t) (WfE:Input.Wf E) :
  Output.Interp (Compile E) = Input.Interp E.
Proof. eapply compile_correct; eauto. Qed.
 *)


Section syn.
  Context {var : vartype -> Type}.
  Inductive syntax :=
  | RegPInv
  | RegMod
  | RegZero
  | RegMuLow
  | cLowerHalf : syntax -> syntax
  | cUpperHalf : syntax -> syntax
  | cLeftShifted : syntax -> Z -> syntax
  | cRightShifted : syntax -> Z -> syntax
  | cVar : var TW -> syntax
  | cVarC : var Tbool -> syntax
  | cBind : syntax -> (var TW -> syntax) -> syntax
  | cBindCarry : syntax -> (var Tbool -> var TW -> syntax) -> syntax
  | cMul128 : syntax -> syntax -> syntax
  | cRshi : syntax -> syntax -> Z -> syntax
  | cSelc : var Tbool -> syntax -> syntax -> syntax
  | cAddc : var Tbool -> syntax -> syntax -> syntax
  | cAddm : syntax -> syntax -> syntax
  | cAdd : syntax -> syntax -> syntax
  | cSub : syntax -> syntax -> syntax
  | cPair : syntax -> syntax -> syntax
  | cAbs {t} : (var t -> syntax) -> syntax
  | cINVALID {T} (_ : T).
End syn.

Definition Syntax := forall var, @syntax var.

Fixpoint assemble_arg {var} {t} (v : @Output.arg (fun _ => @syntax var) t) : @syntax var
  := match v with
     | Output.Const TZ v' => if Z_beq v' 0 then RegZero else cINVALID v'
     | Output.Const _ x => cINVALID x
     | Output.SpZConst Cm => RegMod
     | Output.SpZConst Cμ => RegMuLow
     | Output.Var _ v => v
     | Output.Pair _ x0 _ x1 => cPair (@assemble_arg _ _ x0) (@assemble_arg _ _ x1)
     end.
Definition var_of_arg_helper {var} {t} (v : @Output.arg var t)
  : match t with
    | Prod _ _ => unit
    | Tconst t'
      => match t' with
         | Tvar t'' => var t''
         | TZ => SpecialZConst
         end + interp_type t'
    end.
Proof.
  destruct v;
    try solve [ right; assumption
              | left; assumption
              | exact tt ].
Defined.

Definition assemble_syntax_step
           (assemble_syntax : forall {var} {t} (v : @Output.expr (fun _ => @syntax var) t), @syntax var)
           {var} {t} (v : @Output.expr (fun _ => @syntax var) t) : @syntax var.
Proof.
  refine match v with
         | Output.LetUnop _ op x0 _ b
           => let x0' := assemble_arg x0 in
              match op with
              | OPldi => @assemble_syntax var _ (b x0')
              | _ => cINVALID op
              end
         | Output.LetBinop _ _ op x0 x1 _ b
           => let x0' : @syntax var := assemble_arg x0 in
              let x1' : @syntax var := assemble_arg x1 in
              let default := fun s => cBind s (fun v => @assemble_syntax var _ (b (cVar v))) in
              match op, x1 return @syntax var with
              | OPshl, Output.Const TZ x1'
                => @assemble_syntax var _ (b (cLeftShifted x0' x1'))
              | OPshr, Output.Const TZ x1'
                => @assemble_syntax var _ (b (cRightShifted x0' x1'))
              | OPmulhwll, _
                => default (cMul128 (cLowerHalf x0') (cLowerHalf x1'))
              | OPmulhwhl, _
                => default (cMul128 (cUpperHalf x0') (cLowerHalf x1'))
              | OPmulhwhh, _
                => default (cMul128 (cUpperHalf x0') (cUpperHalf x1'))
              | _, _ => default (cINVALID op)
              end
         | Output.LetTrinop _ _ _ op x0 x1 x2 _ b
           => let x0' : @syntax var := assemble_arg x0 in
              let x1' : @syntax var := assemble_arg x1 in
              let x2' : @syntax var := assemble_arg x2 in
              cBind (match op, x0', x2', x2 return @syntax var with
                     | OPadc, _, _, Output.Const Tbool false
                       => cAdd x0' x1'
                     | OPadc, _, cVarC x2', _
                       => cAddc x2' x0' x1'
                     | OPsubc, _, _, Output.Const Tbool false
                       => cSub x0' x1'
                     | OPselc, cVarC x0', _, _
                       => cSelc x0' x1' x2'
                     | OPaddm, _, RegMod, _
                       => cAddm x0' x1'
                     | OPshrd, _, _, Output.Const TZ z
                       => cRshi x0' x1' z
                     | _, _, _, _ => cINVALID op
                     end)
                    (fun v => @assemble_syntax var _ (b (cVar v)))
         | Output.LetTrinop2Ret _ _ _ op x0 x1 x2 _ b
           => let x0' : @syntax var := assemble_arg x0 in
              let x1' : @syntax var := assemble_arg x1 in
              let x2' : @syntax var := assemble_arg x2 in
              cBindCarry (match op, x0', x2', x2 return @syntax var with
                          | OPadc, _, _, Output.Const Tbool false
                            => cAdd x0' x1'
                          | OPadc, _, cVarC x2', _
                            => cAddc x2' x0' x1'
                          | OPsubc, _, _, Output.Const Tbool false
                            => cSub x0' x1'
                          | _, _, _, _ => cINVALID op
                          end)
                         (fun c v => @assemble_syntax var _ (b (cVarC c) (cVar v)))
         | Output.Return _ x => @assemble_arg var _ x
         | Output.Abs TW d f => cAbs (fun x : var TW => @assemble_syntax var _ (f (cVar x)))
         | Output.Abs s _ _ => cINVALID s
         end.
  exact (fun _ => unit).
Defined.
Fixpoint assemble_syntax {var} {t} (v : @Output.expr (fun _ => @syntax var) t) : @syntax var
  := @assemble_syntax_step (@assemble_syntax) var t v.
Fixpoint AssembleSyntax {t} (v : Output.Expr t) : Syntax
  := fun var => @assemble_syntax var t (v _).

Import Input.

Notation "'ilet' x := 'ldi' v 'in' b" :=
  (Output.LetUnop OPldi (Output.Const v) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'ldi'  v  'in' '//' b").
Notation "'ilet' x := 'ldi' 'm' 'in' b" :=
  (Output.LetUnop OPldi (Output.SpZConst Cm) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'ldi'  'm'  'in' '//' b").
Notation "'ilet' x := 'ldi' 'μ' 'in' b" :=
  (Output.LetUnop OPldi (Output.SpZConst Cμ) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'ldi'  'μ'  'in' '//' b").
Notation "'ilet' x := 'mulhwll' A B 'in' b" :=
  (Output.LetBinop OPmulhwll (Output.Var A) (Output.Var B) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'mulhwll'  A  B  'in' '//' b").
Notation "'ilet' x := 'mulhwhl' A B 'in' b" :=
  (Output.LetBinop OPmulhwhl (Output.Var A) (Output.Var B) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'mulhwhl'  A  B  'in' '//' b").
Notation "'ilet' x := 'mulhwhh' A B 'in' b" :=
  (Output.LetBinop OPmulhwhh (Output.Var A) (Output.Var B) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'mulhwhh'  A  B  'in' '//' b").
Notation "'ilet' x := 'shl' A B 'in' b" :=
  (Output.LetBinop OPshl (Output.Var A) (Output.Const B) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'shl'  A  B  'in' '//' b").
Notation "'ilet' x := 'shr' A B 'in' b" :=
  (Output.LetBinop OPshr (Output.Var A) (Output.Const B) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'shr'  A  B  'in' '//' b").
Notation "'ilet' x := 'shrd' A B C 'in' b" :=
  (Output.LetTrinop OPshrd (Output.Var A) (Output.Var B) (Output.Const C) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'shrd'  A  B  C  'in' '//' b").
Notation "'clet' ( c , x ) := 'adc' A B C 'in' b" :=
  (Output.LetTrinop2Ret OPadc (Output.Var A) (Output.Var B) (Output.Var C) (fun c x => b))
    (at level 200, b at level 200, format "'clet'  ( c ,  x )  :=  'adc'  A  B  C  'in' '//' b").
Notation "'clet' ( c , x ) := 'subc' A B C 'in' b" :=
  (Output.LetTrinop2Ret OPsubc (Output.Var A) (Output.Var B) (Output.Var C) (fun c x => b))
    (at level 200, b at level 200, format "'clet'  ( c ,  x )  :=  'subc'  A  B  C  'in' '//' b").
Notation "'clet' ( c , x ) := 'add' A B 'in' b" :=
  (Output.LetTrinop2Ret OPadc (Output.Var A) (Output.Var B) (Output.Const false) (fun c x => b))
    (at level 200, b at level 200, format "'clet'  ( c ,  x )  :=  'add'  A  B  'in' '//' b").
Notation "'clet' ( c , x ) := 'sub' A B 'in' b" :=
  (Output.LetTrinop2Ret OPsubc (Output.Var A) (Output.Var B) (Output.Const false) (fun c x => b))
    (at level 200, b at level 200, format "'clet'  ( c ,  x )  :=  'sub'  A  B  'in' '//' b").
Notation "'ilet' x := 'selc' A B C 'in' b" :=
  (Output.LetTrinop OPselc (Output.Var A) (Output.Var B) (Output.Var C) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'selc'  A  B  C  'in' '//' b").
Notation "'ilet' x := 'addm' A B C 'in' b" :=
  (Output.LetTrinop OPaddm (Output.Var A) (Output.Var B) (Output.Var C) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'addm'  A  B  C  'in' '//' b").
Notation Return x := (Output.Return (Output.Var x)).
Notation "'λ'  x .. y , t" := (Output.Abs (fun x => .. (Output.Abs (fun y => t)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition compiled_example : Output.Expr (Arrow TW (Arrow TW TW))
  := Eval vm_compute in
      CSE (Compile example_Expr).
Definition compiled_example_syn : Syntax
  := Eval vm_compute in
      AssembleSyntax compiled_example.
Print compiled_example.

(* compiled_example =
fun var : vartype -> Type =>
λ x x0 : var TW,
ilet x1 := ldi 0 in
ilet x2 := ldi m in
ilet x3 := ldi μ in
ilet x4 := shrd x0 x 250 in
ilet x5 := mulhwhh x4 x3 in
ilet x6 := mulhwhl x4 x3 in
ilet x7 := shr x6 128 in
ilet x8 := mulhwll x4 x3 in
ilet x9 := shl x6 128 in
clet (x10, x11) := add x8 x9 in
clet (_, x13) := adc x5 x7 x10 in
ilet x14 := mulhwhl x3 x4 in
ilet x15 := shr x14 128 in
ilet x16 := shl x14 128 in
clet (x17, _) := add x11 x16 in
clet (_, x20) := adc x13 x15 x17 in
ilet x21 := mulhwll x20 x2 in
ilet x22 := mulhwhl x20 x2 in
ilet x23 := shl x22 128 in
clet (_, x25) := add x21 x23 in
ilet x26 := mulhwhl x2 x20 in
ilet x27 := shl x26 128 in
clet (_, x29) := add x25 x27 in
clet (_, x31) := sub x x29 in
ilet x32 := addm x31 x1 x2 in
ilet x33 := addm x32 x1 x2 in
Return x33
     : Output.Expr (Arrow TW (Arrow TW TW))
 *)


Theorem sanity : Output.Interp compiled_example = (fun x y => f (x, y)).
Proof.
  reflexivity.
Qed.

Infix "≡" := (ZUtil.Z.equiv_modulo m).
Infix "≡₂₅₆" := (ZUtil.Z.equiv_modulo (2^256)) (at level 70).

Theorem correctness
        (x y : fancy_machine.W)
        (decoded_input := DoubleBounded.tuple_decoder (k:=2) (x, y))
        (Hxy : 0 <= decoded_input < 2^256 * 2^250)
        (res := fancy_machine.decode (Output.Interp compiled_example x y))
  : res = decoded_input mod m.
Proof.
  subst res decoded_input; rewrite sanity.
  unfold f, fst', snd'; simpl @fst; simpl @snd.
  match goal with |- appcontext[proj1_sig ?x] => pose proof (proj2_sig x) as H' end.
  apply H', Hxy.
Qed.

Print Assumptions correctness.

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

Notation "'c.Rshi' ( x , A , B , C ) , b" :=
  (cBind (cRshi (cVar A) (cVar B) C) (fun x => b))
    (at level 200, b at level 200, format "'c.Rshi' ( x ,  A ,  B ,  C ) , '//' b").

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

Print compiled_example_syn.
(* compiled_example_syn =
fun var : vartype -> Type =>
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
     : Syntax
 *)
