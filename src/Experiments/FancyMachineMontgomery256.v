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

Definition Syntax := forall var, @syntax var.

Notation RegPInvPlaceholder := 1%Z.
Notation RegModPlaceholder := 2%Z.

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
                  | OPldi    , cConstZ RegPInvPlaceholder => RegPInv
                  | OPldi    , cConstZ RegModPlaceholder => RegMod
                  | OPldi    , cConstZ v => cINVALID v
                  | OPshrd   , _ => cINVALID op
                  | OPshl    , cPair w (cConstZ n) => cLeftShifted w n
                  | OPshr    , cPair w (cConstZ n) => cRightShifted w n
                  | OPmkl    , _ => cINVALID op
                  | OPadc    , cPair (cVarC c) (cPair x y) => cAddc c x y
                  | OPadc    , cPair (cConstBool false) (cPair x y) => cAdd x y
                  | OPsubc   , _ => _
                  | OPmulhwll, _ => _
                  | OPmulhwhl, _ => _
                  | OPmulhwhh, _ => _
                  | OPselc   , cPair (cVarC c) (cPair x y) => cSelc c x y
                  | OPaddm   , _ => _
                  | _, _ => cINVALID op
                  end
             | Syntax.Let _ ex _ eC
               => cBind (@assemble_syntaxf _ ex) (fun x => @assemble_syntaxf _ (eC _))
             | Syntax.Pair _ ex _ ey
               => cPair (@assemble_syntaxf _ ex) (@assemble_syntaxf _ ey)
             end.
Focus 2.
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


Fixpoint assemble_arg {var} {t} (v : @Output.arg (fun _ => @syntax var) t) : @syntax var
  := match v with
     | Output.Const TZ v' => if Z_beq v' 0 then RegZero else cINVALID v'
     | Output.Const _ x => cINVALID x
     | Output.SpZConst Cm' => RegPInv
     | Output.SpZConst Cmodulus => RegMod
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
Notation "'ilet' x := 'ldi' 'm'' 'in' b" :=
  (Output.LetUnop OPldi (Output.SpZConst Cm') (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'ldi'  'm''  'in' '//' b").
Notation "'ilet' x := 'ldi' 'modulus' 'in' b" :=
  (Output.LetUnop OPldi (Output.SpZConst Cmodulus) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'ldi'  'modulus'  'in' '//' b").
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
ilet x2 := ldi modulus in
ilet x3 := ldi m' in
ilet x4 := mulhwll x x3 in
ilet x5 := mulhwhl x x3 in
ilet x6 := shl x5 128 in
clet (_, x8) := add x4 x6 in
ilet x9 := mulhwhl x3 x in
ilet x10 := shl x9 128 in
clet (_, x12) := add x8 x10 in
ilet x13 := mulhwhh x12 x2 in
ilet x14 := mulhwhl x12 x2 in
ilet x15 := shr x14 128 in
ilet x16 := mulhwll x12 x2 in
ilet x17 := shl x14 128 in
clet (x18, x19) := add x16 x17 in
clet (_, x21) := adc x13 x15 x18 in
ilet x22 := mulhwhl x2 x12 in
ilet x23 := shr x22 128 in
ilet x24 := shl x22 128 in
clet (x25, x26) := add x19 x24 in
clet (_, x28) := adc x21 x23 x25 in
clet (x29, _) := add x x26 in
clet (x31, x32) := adc x0 x28 x29 in
ilet x33 := selc x31 x2 x1 in
clet (_, x35) := sub x32 x33 in
ilet x36 := addm x35 x1 x2 in
Return x36
     : Output.Expr (Arrow TW (Arrow TW TW))

 *)


Notation "'ilet' x := 'ldi' v 'in' b" :=
  (Output.LetUnop OPldi (Output.Const v) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'ldi'  v  'in' '//' b").
Notation "'ilet' x := 'ldi' 'm'' 'in' b" :=
  (Output.LetUnop OPldi (Output.SpZConst Cm') (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'ldi'  'm''  'in' '//' b").
Notation "'ilet' x := 'ldi' 'modulus' 'in' b" :=
  (Output.LetUnop OPldi (Output.SpZConst Cmodulus) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'ldi'  'modulus'  'in' '//' b").
Notation "'c.Mul128' ( x , 'c.LowerHalf' ( A ) , 'c.LowerHalf' ( B ) ) , b" :=
  (Output.LetBinop OPmulhwll (Output.Var A) (Output.Var B) (fun x => b))
    (at level 200, b at level 200, A at level 0, B at level 0, format "'c.Mul128' ( x ,  'c.LowerHalf' ( A ) ,  'c.LowerHalf' ( B ) ) , '//' b").
Notation "'c.Mul128' ( x , 'c.UpperHalf' ( A ) , 'c.LowerHalf' ( B ) ) , b" :=
  (Output.LetBinop OPmulhwhl (Output.Var A) (Output.Var B) (fun x => b))
    (at level 200, b at level 200, A at level 0, B at level 0, format "'c.Mul128' ( x ,  'c.UpperHalf' ( A ) ,  'c.LowerHalf' ( B ) ) , '//' b").
Notation "'c.Mul128' ( x , 'c.UpperHalf' ( A ) , 'c.UpperHalf' ( B ) ) , b" :=
  (Output.LetBinop OPmulhwhh (Output.Var A) (Output.Var B) (fun x => b))
    (at level 200, b at level 200, A at level 0, B at level 0, format "'c.Mul128' ( x ,  'c.UpperHalf' ( A ) ,  'c.UpperHalf' ( B ) ) , '//' b").
Notation "'let' x := 'c.LeftShifted' { A , B } 'in' b" :=
  (Output.LetBinop OPshl (Output.Var A) (Output.Const B) (fun x => b))
    (at level 200, b at level 200, format "'let'  x  :=  'c.LeftShifted' { A ,  B }  'in' '//' b").
Notation "'let' x := 'c.RightShifted' { A , B } 'in' b" :=
  (Output.LetBinop OPshr (Output.Var A) (Output.Const B) (fun x => b))
    (at level 200, b at level 200, format "'let'  x  :=  'c.RightShifted' { A ,  B }  'in' '//' b").
Notation "'clet' ( c , x ) := 'adc' A B C 'in' b" :=
  (Output.LetTrinop2Ret OPadc (Output.Var A) (Output.Var B) (Output.Var C) (fun c x => b))
    (at level 200, b at level 200, format "'clet'  ( c ,  x )  :=  'adc'  A  B  C  'in' '//' b").
Notation "'clet' ( c , x ) := 'subc' A B C 'in' b" :=
  (Output.LetTrinop2Ret OPsubc (Output.Var A) (Output.Var B) (Output.Var C) (fun c x => b))
    (at level 200, b at level 200, format "'clet'  ( c ,  x )  :=  'subc'  A  B  C  'in' '//' b").
Notation "'clet' ( c , x ) := 'add' A B 'in' b" :=
  (Output.LetTrinop2Ret OPadc (Output.Var A) (Output.Var B) (Output.Const false) (fun c x => b))
    (at level 200, b at level 200, format "'clet'  ( c ,  x )  :=  'add'  A  B  'in' '//' b").

Notation "'c.Add' ( x , A , B ) , b" :=
  (Output.LetTrinop2Ret OPadc (Output.Var A) (Output.Var B) (Output.Const false) (fun _ x => b))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' b").

Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x' , A' , B' ) , b" :=
  (Output.LetTrinop2Ret OPadc (Output.Var A) (Output.Var B) (Output.Const false) (fun c x => (Output.LetTrinop2Ret OPadc (Output.Var A') (Output.Var B') (Output.Var c) (fun _ x' => b))))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x' ,  A' ,  B' ) , '//' b").

Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x' , A' , B' ) , 'c.Selc' ( x'' , A'' , B'' ) , b" :=
  (Output.LetTrinop2Ret OPadc (Output.Var A) (Output.Var B) (Output.Const false) (fun c x => (Output.LetTrinop2Ret OPadc (Output.Var A') (Output.Var B') (Output.Var c) (fun c' x' => (Output.LetTrinop OPselc (Output.Var c') (Output.Var A'') (Output.Var B'') (fun x'' => b))))))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x' ,  A' ,  B' ) , '//' 'c.Selc' ( x'' ,  A'' ,  B'' ) , '//' b").

Notation "'c.Sub' ( x , A , B ) , b" :=
  (Output.LetTrinop2Ret OPsubc (Output.Var A) (Output.Var B) (Output.Const false) (fun _ x => b))
    (at level 200, b at level 200, format "'c.Sub' ( x ,  A ,  B ) , '//' b").
Print compiled_example.

Theorem sanity : Output.Interp compiled_example = (fun x y => f (x, y)).
Proof.
  reflexivity.
Qed.

Infix "≡" := (ZUtil.Z.equiv_modulo modulus).
Infix "≡₂₅₆" := (ZUtil.Z.equiv_modulo (2^256)) (at level 70).

Theorem correctness
        (R' : Z)
        (Hmod : 2^256 * R' ≡ 1)
        (Hmod' : modulus * m' ≡₂₅₆ -1)
        (x y : fancy_machine.W)
        (decoded_input := DoubleBounded.tuple_decoder (k:=2) (x, y))
        (Hxy : 0 <= decoded_input <= 2^256 * modulus)
        (res := fancy_machine.decode (Output.Interp compiled_example x y))
  : res ≡ decoded_input * R'
    /\ 0 <= res < modulus.
Proof.
  subst res decoded_input; rewrite sanity.
  pose proof (@Montgomery.ZBounded.reduce_via_partial_correct _ _ _ props') as H'.
  unfold ZBounded.decode_small, ZBounded.decode_large, ZLikeOps_of_ArchitectureBoundedOps in *.
  unfold f, fst', snd', fst, snd in *.
  eapply H'; eauto using Hm, Hm', @decode_range_bound.
  { replace (fancy_machine.decode (ldi m')) with m'.
    { assumption. }
    { symmetry; apply (decode_load_immediate _ _), Hm'. } }
  { exact I. }
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
