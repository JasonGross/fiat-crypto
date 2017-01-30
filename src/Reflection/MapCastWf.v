Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Reflection.MapCast.
Require Import Crypto.Reflection.WfProofs.
Require Import Crypto.Reflection.WfInversion.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.

Local Open Scope ctype_scope.
Local Open Scope expr_scope.
Section language.
  Context {base_type_code : Type}
          {interp_base_type : base_type_code -> Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (interp_op2 : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst)
          (failv : forall {var t}, @exprf base_type_code op var (Tbase t))
          (new_base_type : forall t, interp_base_type t -> base_type_code).
  Local Notation new_flat_type (*: forall t, interp_flat_type interp_base_type2 t -> flat_type base_type_code1*)
    := (@SmartFlatTypeMap2 _ _ interp_base_type (fun t v => Tbase (new_base_type t v))).
  Context (transfer_op : forall ovar src1 dst1 src2 dst2
                                (opc1 : op src1 dst1)
                                (opc2 : op src2 dst2)
                                args2
                                (args' : @exprf base_type_code op ovar (@new_flat_type _ (interpf interp_op2 args2))),
              @exprf base_type_code op ovar (@new_flat_type _ (interpf interp_op2 (Op opc2 args2)))).

  Local Notation interp_flat_type_ivarf_wff G a b
    := (forall t x y,
           List.In (existT _ t (x, y)%core) (flatten_binding_list a b)
           -> wff G x y)
         (only parsing).

  Section with_var.
    Context {ovar1 ovar2 : base_type_code -> Type}.
    Local Notation ivar1 t := (@exprf base_type_code op ovar1 (Tbase t)) (only parsing).
    Local Notation ivar2 t := (@exprf base_type_code op ovar2 (Tbase t)) (only parsing).
    Local Notation ivarf1 := (fun t => ivar1 t).
    Local Notation ivarf2 := (fun t => ivar2 t).
    Context (transfer_var11 : forall tx1 tx2
                                     (v1 : ivar1 tx1)
                                     (v2 : interp_base_type tx2),
                exprf base_type_code op (var:=ovar1) (Tbase (new_base_type tx2 v2))).
    Context (transfer_var12 : forall tx1 tx2
                                     (v1 : ivar2 tx1)
                                     (v2 : interp_base_type tx2),
                exprf base_type_code op (var:=ovar2) (Tbase (new_base_type tx2 v2))).
    Context (transfer_var21 : forall tx1 tx' tC'
                                     (ex' : interp_flat_type interp_base_type tx')
                                     (eC' : interp_flat_type interp_base_type tx' -> exprf base_type_code op tC')
                                     (f : interp_flat_type ivarf1 tx1 -> exprf base_type_code op (var:=ovar1) (new_flat_type (interpf interp_op2 (eC' ex'))))
                                     (v : interp_flat_type ovar1 (new_flat_type ex')),
                exprf base_type_code op (var:=ovar1) (new_flat_type (interpf interp_op2 (eC' ex')))).
    Context (transfer_var22 : forall tx1 tx' tC'
                                     (ex' : interp_flat_type interp_base_type tx')
                                     (eC' : interp_flat_type interp_base_type tx' -> exprf base_type_code op tC')
                                     (f : interp_flat_type ivarf2 tx1 -> exprf base_type_code op (var:=ovar2) (new_flat_type (interpf interp_op2 (eC' ex'))))
                                     (v : interp_flat_type ovar2 (new_flat_type ex')),
                exprf base_type_code op (var:=ovar2) (new_flat_type (interpf interp_op2 (eC' ex')))).

    Context (wff_transfer_op
             : forall G src1 dst1 src2 dst2 opc1 opc2 args2 e1 e2,
                wff G (var1:=ovar1) (var2:=ovar2) e1 e2
                -> wff G
                       (@transfer_op ovar1 src1 dst1 src2 dst2 opc1 opc2 args2 e1)
                       (@transfer_op ovar2 src1 dst1 src2 dst2 opc1 opc2 args2 e2)).
    Context (wff_transfer_var1
             : forall G t x1 x2 v,
                wff G x1 x2
                -> wff G
                       (@transfer_var11 t t x1 v)
                       (@transfer_var12 t t x2 v)).
    Context (wff_transfer_var2
             : forall G tx tC ex' eC' f g (v1 : interp_flat_type ovar1 _) v2,
                (forall a b,
                    interp_flat_type_ivarf_wff G a b
                    -> wff G (f a) (g b))
                -> wff (op:=op) G (SmartVarf v1) (SmartVarf v2)
                -> wff G
                       (@transfer_var21 tx tx tC ex' eC' f v1)
                       (@transfer_var22 tx tx tC ex' eC' g v2)).
    Local Notation mapf_interp_cast
      := (@mapf_interp_cast
            base_type_code base_type_code interp_base_type
            op op interp_op2 failv new_base_type
            transfer_op).
    Local Notation map_interp_cast
      := (@map_interp_cast
            base_type_code base_type_code interp_base_type
            op op interp_op2 failv new_base_type
            transfer_op).

    Local Notation G1eTf
      := (fun t : base_type_code => interp_flat_type ivarf1 (Tbase t) * interp_flat_type ivarf2 (Tbase t))%type.
    Local Notation G2eTf
      := (fun t : base_type_code => ovar1 t * ovar2 t)%type.
    Local Notation GbeTf
      := (fun t : base_type_code => interp_flat_type ivarf1 (Tbase t) * interp_base_type t)%type.

    (*  Definition Gse_related' {t} (G1e : G1eTf t) (Gbe : GbeTf t) (G2e G2eTf t) : Prop
    := fst G1e = fst Gbe /\

    := exists (pf1 : projT1 G1e = projT1 G2e

                                         Definition Gse_related (G1e : sigT G1eTf) (G2e : sigT G2eTf) (G3e : sigT G3eTf) : Prop
    := exists (pf1 : projT1 G1e = projT1 G2e
                   /\

  Local Notation G3eT
    := {t : base_type_code &
            ((interp_flat_type ivarf1 (Tbase t) * interp_flat_type ivarf2 (Tbase t))
             * (ovar1 t * ovar2 t)
             * interp_base_type t)%type }.
  Local Notation G3T
    := (list G3eT).

  Definition G3e_to_G1e

     *)
    (* Local *) Hint Resolve <- List.in_app_iff.

    Local Ltac break_t
      := first [ progress subst
               | progress inversion_wf
               | progress invert_expr_subst
               | progress inversion_sigma
               | progress inversion_prod
               | progress destruct_head sig
               | progress destruct_head sigT
               | progress destruct_head ex
               | progress destruct_head and
               | progress destruct_head prod
               | progress break_match_hyps ].

    Lemma wff_mapf_interp_cast
          G1 Gbounds G2
          (H_G1_G2
           : forall t x y,
              List.In (existT _ t (x, y)%core) G1
              -> wff G2 x y)
          {t1} e1 e2 ebounds
          (Hwf_bounds : wff Gbounds e1 ebounds)
          (Hwf : wff G1 e1 e2)
      : wff G2
            (@mapf_interp_cast ovar1 transfer_var11 transfer_var21 t1 e1 t1 ebounds)
            (@mapf_interp_cast ovar2 transfer_var12 transfer_var22 t1 e2 t1 ebounds).
    Proof.
      revert dependent Gbounds; revert ebounds; revert dependent G2.
      induction Hwf;
        repeat match goal with
               | _ => solve [ exfalso; assumption ]
               | _ => intro
               | _ => progress break_t
               | _ => solve [ constructor; eauto
                            | eauto
                            | auto
                            | hnf; auto ]
               | _ => progress simpl in *
               | [ |- wff _ (transfer_var11 _ _ _ _ _) (transfer_var12 _ _ _ _ _) ]
                 => apply wff_transfer_var1
               | [ |- wff _ (transfer_var21 _ _ _ _ _ _ _) (transfer_var22 _ _ _ _ _ _ _) ]
                 => apply wff_transfer_var2
               | [ H : List.In _ (_ ++ _) |- _ ] => apply List.in_app_or in H
               | _ => progress destruct_head or
               | [ |- wff _ _ _ ] => constructor
               | [ H : _ |- wff _ (mapf_interp_cast _ _ _ _) (mapf_interp_cast _ _ _ _) ]
                 => eapply H; eauto; []; clear H
               | _ => solve [ eauto using wff_SmartVarf, wff_in_impl_Proper ]
               end.
    Qed.

    Lemma wf_map_interp_cast
          {t1} e1 e2 ebounds
          args2
          (Hwf_bounds : wf e1 ebounds)
          (Hwf : wf e1 e2)
      : wf (@map_interp_cast ovar1 transfer_var11 transfer_var21 t1 e1 t1 ebounds args2)
           (@map_interp_cast ovar2 transfer_var12 transfer_var22 t1 e2 t1 ebounds args2).
    Proof.
      destruct Hwf;
        repeat match goal with
               | _ => solve [ constructor; eauto
                            | eauto using wff_mapf_interp_cast
                            | exfalso; assumption ]
               | _ => intro
               | _ => progress break_t
               | [ |- wf _ _ ] => constructor
               | [ |- wff _ (transfer_var21 _ _ _ _ _ _ _) (transfer_var22 _ _ _ _ _ _ _) ]
                 => apply wff_transfer_var2
               | _ => solve [ eauto using wff_SmartVarf, wff_in_impl_Proper ]
               end.
    Qed.
  End with_var.

  Section gen.
    Context (wff_transfer_op
             : forall ovar1 ovar2 G src1 dst1 src2 dst2 opc1 opc2 args2 e1 e2,
                wff G (var1:=ovar1) (var2:=ovar2) e1 e2
                -> wff G
                       (@transfer_op ovar1 src1 dst1 src2 dst2 opc1 opc2 args2 e1)
                       (@transfer_op ovar2 src1 dst1 src2 dst2 opc1 opc2 args2 e2)).
    Context (transfer_var1 : forall ovar tx1 tx2
                                    (ivar := fun t => @exprf base_type_code op ovar (Tbase t))
                                    (v1 : ivar tx1)
                                    (v2 : interp_base_type tx2),
                exprf base_type_code op (var:=ovar) (Tbase (new_base_type tx2 v2))).
    Context (transfer_var2 : forall ovar tx1 tx' tC'
                                    (ivarf := fun t => @exprf base_type_code op ovar (Tbase t))
                                    (ex' : interp_flat_type interp_base_type tx')
                                    (eC' : interp_flat_type interp_base_type tx' -> exprf base_type_code op tC')
                                    (f : interp_flat_type ivarf tx1 -> exprf base_type_code op (var:=ovar) (new_flat_type (interpf interp_op2 (eC' ex'))))
                                    (v : interp_flat_type ovar (new_flat_type ex')),
                exprf base_type_code op (var:=ovar) (new_flat_type (interpf interp_op2 (eC' ex')))).
    Context (wff_transfer_var1
             : forall ovar1 ovar2 G t x1 x2 v,
                wff G x1 x2
                -> wff G
                       (@transfer_var1 ovar1 t t x1 v)
                       (@transfer_var1 ovar2 t t x2 v)).
    Context (wff_transfer_var2
             : forall ovar1 ovar2 G tx tC ex' eC' f g (v1 : interp_flat_type ovar1 _) v2,
                (forall a b,
                    interp_flat_type_ivarf_wff G a b
                    -> wff G (f a) (g b))
                -> wff (op:=op) G (SmartVarf v1) (SmartVarf v2)
                -> wff G
                       (@transfer_var2 ovar1 tx tx tC ex' eC' f v1)
                       (@transfer_var2 ovar2 tx tx tC ex' eC' g v2)).

    Local Notation MapInterpCast
      := (@MapInterpCast
            base_type_code interp_base_type
            op interp_op2 failv new_base_type
            transfer_op transfer_var1 transfer_var2).

    Lemma WfMapInterpCast
          {t} e
          args
          (Hwf : Wf e)
      : Wf (@MapInterpCast t e args).
    Proof.
      intros ??; apply wf_map_interp_cast; auto.
    Qed.
  End gen.
End language.
