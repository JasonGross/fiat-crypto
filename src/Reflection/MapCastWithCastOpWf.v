Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Reflection.MapCastWithCastOp.
Require Import Crypto.Reflection.MapCastWf.
Require Import Crypto.Reflection.WfProofs.
Require Import Crypto.Reflection.WfInversion.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Equality.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.

Local Open Scope ctype_scope.
Local Open Scope expr_scope.
Section language.
  Context {base_type_code : Type}
          {interp_base_type : base_type_code -> Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (interp_op2 : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst)
          (base_type_code_beq : base_type_code -> base_type_code -> bool)
          (base_type_code_bl : forall x y, base_type_code_beq x y = true -> x = y)
          (base_type_code_lb : forall x y, x = y -> base_type_code_beq x y = true)
          (failv : forall {var t}, @exprf base_type_code op var (Tbase t))
          (new_base_type : forall t, interp_base_type t -> base_type_code)
          (Cast : forall var t1 t2, @exprf base_type_code op var (Tbase t1)
                                    -> @exprf base_type_code op var (Tbase t2))
          (is_cast : forall t1 t2, op t1 t2 -> bool).
  Local Notation new_flat_type (*: forall t, interp_flat_type interp_base_type2 t -> flat_type base_type_code1*)
    := (@SmartFlatTypeMap2 _ _ interp_base_type (fun t v => Tbase (new_base_type t v))).
  Context (new_op : forall ovar src1 dst1 src2 dst2 (opc1 : op src1 dst1) (opc2 : op src2 dst2)
                           args2,
              option { new_src : _ & (@exprf base_type_code op ovar new_src
                                      -> @exprf base_type_code op ovar (new_flat_type (interpf interp_op2 (Op opc2 args2))))%type }).
  Local Notation SmartFail
    := (SmartValf _ (@failv _)).
  Local Notation failf t (* {t} : @exprf base_type_code1 op1 ovar t*)
    := (SmartPairf (SmartFail t)).
  Local Notation mapf_interp_cast_with_cast_op
    := (@mapf_interp_cast_with_cast_op
          base_type_code base_type_code interp_base_type
          op op interp_op2
          base_type_code_beq base_type_code_bl
          failv new_base_type Cast is_cast new_op).
  Local Notation map_interp_cast_with_cast_op
    := (@map_interp_cast_with_cast_op
          base_type_code base_type_code interp_base_type
          op op interp_op2
          base_type_code_beq base_type_code_bl
          failv new_base_type Cast is_cast new_op).
  Local Notation bound_op
    := (@bound_op
          base_type_code base_type_code interp_base_type
          op op interp_op2
          base_type_code_beq base_type_code_bl
          failv new_base_type Cast is_cast new_op).
  Local Notation bound_var
    := (@bound_var
          base_type_code
          op
          base_type_code_beq base_type_code_bl
          failv Cast is_cast).

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

    Local Notation G1eTf
      := (fun t : base_type_code => interp_flat_type ivarf1 (Tbase t) * interp_flat_type ivarf2 (Tbase t))%type.
    Local Notation G2eTf
      := (fun t : base_type_code => ovar1 t * ovar2 t)%type.
    Local Notation GbeTf
      := (fun t : base_type_code => interp_flat_type ivarf1 (Tbase t) * interp_base_type t)%type.

    Local Hint Constructors Wf.wff.

    Lemma wff_failf G t
          (wff_failv : forall T, wff G (failv ovar1 T) (failv ovar2 T))
      : wff (t:=t) (var1:=ovar1) (var2:=ovar2) G (failf t) (failf t).
    Proof.
      clear -wff_failv.
      induction t; simpl; rewrite ?SmartPairf_Pair; eauto; constructor.
    Qed.

    Local Hint Resolve wff_failf.

    Local Ltac t_step :=
      match goal with
      | _ => progress simpl
      | _ => progress break_innermost_match
      | _ => solve [ constructor | eauto ]
      | [ |- ?f _ match ?H with eq_refl => ?v1 end match ?H with eq_refl => ?v2 end ]
        => rewrite (@commute_eq_match2 _ _ _ _ f _ _ H v1 v2)
      | _ => rewrite eq_match_const
      | [ wff_Cast : forall t1 t2 a b, wff _ _ _ -> wff _ (Cast _ _ _ _) (Cast _ _ _ _)
                                       |- wff _ (Cast _ _ _ _) (Cast _ _ _ _) ]
        => apply wff_Cast
      | _ => rewrite SmartPairf_Pair
      | _ => progress specialize_by auto
      | [ Hxy : forall k, List.In k _ -> List.In k ?G |- List.In _ ?G ]
        => apply Hxy
      | [ |- context[List.In _ (_ ++ _)] ] => rewrite List.in_app_iff
      | [ |- wff _ _ _ ] => constructor
      | [ |- wff _ _ _ ] => eapply wff_in_impl_Proper; [ solve [ eauto with nocore ] | ]
      | _ => intro
      end.

    Lemma wff_VarBound G a b x y
          (wff_failv : forall T, wff G (failv ovar1 T) (failv ovar2 T))
          (wff_Cast : forall t1 t2 a b, wff G a b -> wff G (Cast ovar1 t1 t2 a)
                                                         (Cast ovar2 t1 t2 b))
          (Hxy : forall k, List.In k (flatten_binding_list x y) -> List.In k G)
      : wff G
            (VarBound failv Cast (var:=ovar1) a b x)
            (VarBound failv Cast (var:=ovar2) a b y).
    Proof.
      clear -wff_failv wff_Cast Hxy.
      revert dependent b; induction a;
        repeat match goal with
               | _ => progress t_step
               | [ H : _ |- _ ] => apply H
               end.
    Qed.

    Lemma wff_SmartBound G t1 t2 e1 e2
          (wff_failv : forall T, wff G (failv ovar1 T) (failv ovar2 T))
          (wff_Cast : forall G t1 t2 a b, wff G a b -> wff G (Cast ovar1 t1 t2 a)
                                                         (Cast ovar2 t1 t2 b))
          (Hwf : wff (t:=t1) G e1 e2)
      : wff (t:=t2) G
            (SmartBound (var:=ovar1) base_type_code_beq base_type_code_bl failv Cast is_cast e1)
            (SmartBound (var:=ovar2) base_type_code_beq base_type_code_bl failv Cast is_cast e2).
    Proof.
      clear -wff_failv wff_Cast Hwf.
      revert dependent t2; induction Hwf; intros; specialize_by auto;
        induction t2;
        repeat match goal with
               | [ |- wff _ (VarBound _ _ _ _ _) (VarBound _ _ _ _ _) ]
                 => apply wff_VarBound
               | _ => progress t_step
               end.
    Qed.

    Section with_assumptions.
      Context (wff_failv : forall G T, wff G (failv ovar1 T) (failv ovar2 T))
              (wff_Cast : forall G t1 t2 a b,
                  wff G a b -> wff G (Cast ovar1 t1 t2 a) (Cast ovar2 t1 t2 b))
              (wff_new_op
               : forall G src1 dst1 src2 dst2 opc1 opc2 args0
                        (v1 : forall t, exprf _ _ t)
                        (v2 : forall t, exprf _ _ t),
                  (forall t, wff G (v1 t) (v2 t))
                  -> match new_op ovar1 src1 dst1 src2 dst2 opc1 opc2 args0, new_op ovar2 src1 dst1 src2 dst2 opc1 opc2 args0 with
                     | Some f, Some g => wff G (projT2 f (v1 (projT1 f))) (projT2 g (v2 (projT1 g)))
                     | None, None => True
                     | Some _, None | None, Some _ => False
                     end).

      Lemma wff_bound_op
            G src1 dst1 src2 dst2 opc1 opc2 args2 e1 e2
            (Hwf : wff G (var1:=ovar1) (var2:=ovar2) e1 e2)
        : wff G
              (@bound_op ovar1 src1 dst1 src2 dst2 opc1 opc2 args2 e1)
              (@bound_op ovar2 src1 dst1 src2 dst2 opc1 opc2 args2 e2).
      Proof.
        specialize (wff_new_op G src1 dst1 src2 dst2 opc1 opc2 args2).
        unfold MapCastWithCastOp.bound_op.
        repeat match goal with
               | _ => solve [ eauto using wff_SmartBound | exfalso; assumption ]
               | _ => progress specialize_by eauto
               | [ |- wff ?G (projT2 ?f ?a) (projT2 ?g ?b) ]
                 => let a := match (eval pattern (projT1 f) in a) with ?a _ => a end in
                    let b := match (eval pattern (projT1 g) in b) with ?b _ => b end in
                    specialize (wff_new_op a b)
               | _ => progress break_match_step ltac:(fun _ => idtac)
                   | [ |- wff ?G _ _ ] => specialize (wff_new_op (fun t => failf t) (fun t => failf t))
               end.
      Qed.

      Local Hint Resolve wff_bound_op.

      Lemma wff_bound_var
            G tx1 tx2 tC1 f1 f2 e1 e2
            (Hwfe : interp_flat_type_ivarf_wff G e1 e2)
            (Hwff : forall x y, interp_flat_type_ivarf_wff G x y -> wff G (f1 x) (f2 y))
        : wff G
              (@bound_var ovar1 tx1 tx2 tC1 f1 e1)
              (@bound_var ovar2 tx1 tx2 tC1 f2 e2).
      Proof.
        revert dependent tx1.
        induction tx2;
          repeat match goal with
                 | _ => progress subst
                 | _ => progress inversion_sigma
                 | _ => progress inversion_prod
                 | _ => progress destruct_head' ex
                 | _ => progress destruct_head' and
                 | _ => progress break_match_step ltac:(fun _ => idtac)
                 | [ H : False |- _ ] => exfalso; assumption
                 | [ H : context[List.In _ (_ ++ _)] |- _ ]
                   => rewrite List.in_app_iff in H
                 | [ H : context[List.In _ (_ ++ _)] |- _ ]
                   => setoid_rewrite List.in_app_iff in H
                 | [ H : forall x y, _ -> wff ?G (?f1 _) (?f2 _) |- wff ?G (?f1 _) (?f2 _) ]
                   => apply H; clear H
                 | [ |- wff _ (SmartBound _ _ _ _ _ _) (SmartBound _ _ _ _ _ _) ]
                   => apply wff_SmartBound
                 | _ => intro
                 | _ => solve [ eauto ]
                 | _ => progress simpl in *
                 | _ => progress destruct_head' or
                 | [ H : context[flatten_binding_list (SmartValf _ _ _) (SmartValf _ _ _)] |- _ ]
                   => rewrite flatten_binding_list_SmartValf in H
                 | [ H : List.In _ (List.map _ _) |- _ ]
                   => rewrite List.in_map_iff in H
                 | [ H : _ |- wff _ (bound_var _ _ _ _ _) (bound_var _ _ _ _ _) ]
                   => apply H; clear H
                 end.
      Qed.

      Local Hint Resolve wff_bound_var.

      Lemma wf_map_interp_cast_with_cast_op
            {t1} e1 e2 ebounds args
            (Hwf_bounds : wf e1 ebounds)
            (Hwf : wf e1 e2)
        : wf (@map_interp_cast_with_cast_op ovar1 t1 e1 t1 ebounds args)
             (@map_interp_cast_with_cast_op ovar2 t1 e2 t1 ebounds args).
      Proof.
        eapply wf_map_interp_cast; eauto.
      Qed.
    End with_assumptions.
  End with_var.

  Section gen.
    Context (wff_failv : forall ovar1 ovar2 G T, wff G (failv ovar1 T) (failv ovar2 T))
            (wff_Cast : forall ovar1 ovar2 G t1 t2 a b,
                wff G a b -> wff G (Cast ovar1 t1 t2 a) (Cast ovar2 t1 t2 b))
            (wff_new_op
             : forall ovar1 ovar2 G src1 dst1 src2 dst2 opc1 opc2 args0
                      (v1 : forall t, exprf _ _ t)
                      (v2 : forall t, exprf _ _ t),
                (forall t, wff G (v1 t) (v2 t))
                -> match new_op ovar1 src1 dst1 src2 dst2 opc1 opc2 args0, new_op ovar2 src1 dst1 src2 dst2 opc1 opc2 args0 with
                   | Some f, Some g => wff G (projT2 f (v1 (projT1 f))) (projT2 g (v2 (projT1 g)))
                   | None, None => True
                   | Some _, None | None, Some _ => False
                   end).

    Local Notation MapInterpCastWithCastOp
      := (@MapInterpCastWithCastOp
            base_type_code interp_base_type
            op interp_op2
            base_type_code_beq base_type_code_bl
            failv new_base_type Cast is_cast new_op).

    Lemma WfMapInterpCastWithCastOp
          {t} e
          args
          (Hwf : Wf e)
      : Wf (@MapInterpCastWithCastOp t e args).
    Proof.
      intros ??; apply wf_map_interp_cast_with_cast_op; eauto;
        apply wff_new_op.
    Qed.
  End gen.
End language.
