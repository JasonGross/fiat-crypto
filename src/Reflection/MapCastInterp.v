Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Reflection.MapCast.
Require Import Crypto.Reflection.Relations.
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
          {interp_base_type1 : base_type_code -> Type}
          {interp_base_type2 : base_type_code -> Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (interp_op1 : forall src dst, op src dst -> interp_flat_type interp_base_type1 src -> interp_flat_type interp_base_type1 dst)
          (interp_op2 : forall src dst, op src dst -> interp_flat_type interp_base_type2 src -> interp_flat_type interp_base_type2 dst)
          (failv : forall {var t}, @exprf base_type_code op var (Tbase t))
          (new_base_type : forall t, interp_base_type2 t -> base_type_code).
  Local Notation new_flat_type (*: forall t, interp_flat_type interp_base_type2 t -> flat_type base_type_code1*)
    := (@SmartFlatTypeMap2 _ _ interp_base_type2 (fun t v => Tbase (new_base_type t v))).
  Context (transfer_op : forall ovar src1 dst1 src2 dst2
                                (opc1 : op src1 dst1)
                                (opc2 : op src2 dst2)
                                args2
                                (args' : @exprf base_type_code op ovar (@new_flat_type _ (interpf interp_op2 args2))),
              @exprf base_type_code op ovar (@new_flat_type _ (interpf interp_op2 (Op opc2 args2)))).
  Context (R' : forall t1 t2, interp_base_type1 t1 -> interp_base_type2 t2 -> Prop).
  Local Notation Rt t1 t2 x y (*t1 t2 (x : interp_flat_type interp_base_type1 t1) (y : interp_flat_type interp_base_type2 t2)*)
    := (interp_flat_type_rel_pointwise2_hetero (t1:=t1) (t2:=t2) R' x y).
  Local Notation R x y := (Rt _ _ x y).
  Local Notation RTt t1 t2 x y
    := (interp_type_rel_pointwise2_hetero (t1:=t1) (t2:=t2) R' x y).
  Local Notation RT x y := (RTt _ _ x y).

  (*Local Notation interp_flat_type_ivarf_wff G a b
    := (forall t x y,
           List.In (existT _ t (x, y)%core) (flatten_binding_list a b)
           -> wff G x y)
         (only parsing).*)
  Local Notation interp_flat_type_ivarf_Rb a b
    := (forall t x y,
           List.In (existT _ t (x, y)%core) (flatten_binding_list a b)
           -> Rt _ (Tbase _) (interpf interp_op1 x) y)
         (only parsing).
  Local Notation interp_flat_type_ivarf_R a b
    := (forall t x y,
           List.In (existT _ t (x, y)%core) (flatten_binding_list a b)
           -> R (interpf interp_op1 x) y)
         (only parsing).
  Local Notation interp_flat_type_ivarf_R2b a b
    := (forall t1 t2 x y,
           List.In (existT _ (t1, t2)%core (x, y)%core) (flatten_binding_list2 a b)
           -> Rt _ (Tbase _) (interpf interp_op1 x) y)
         (only parsing).
  Local Notation interp_flat_type_ivarf_R2 a b
    := (forall t1 t2 x y,
           List.In (existT _ (t1, t2)%core (x, y)%core) (flatten_binding_list2 a b)
           -> R (interpf interp_op1 x) y)
         (only parsing).

  Context (Rinterp_op : forall src dst opc args1 args2,
              R args1 args2 -> R (interp_op1 src dst opc args1) (interp_op2 src dst opc args2))
          (Rtransfer_op : forall src dst
                                 (opc : op src dst)
                                 args2
                                 (args' : @exprf base_type_code op interp_base_type1 (@new_flat_type _ (interpf interp_op2 args2))),
              R (interpf interp_op1 args') (interpf interp_op2 args2)
              -> R (interpf interp_op1 (transfer_op _ src dst src dst opc opc args2 args'))
                   (interpf interp_op2 (Op opc args2))).

  Local Notation ivar t := (@exprf base_type_code op interp_base_type1 (Tbase t)) (only parsing).
  Local Notation ivarf := (fun t => ivar t).
  Section with_var.
    Context (transfer_var : forall tx1 tx2 tC1
                                   (f : interp_flat_type ivarf tx1 -> exprf base_type_code op (var:=interp_base_type1) tC1)
                                   (v : interp_flat_type ivarf tx2),
                exprf base_type_code op (var:=interp_base_type1) tC1).

    Context (R_transfer_var
             : forall tx1 tx1' tx2 tC1 tC2
                      (f : interp_flat_type ivarf tx1 -> exprf base_type_code op tC1)
                      (g : interp_flat_type interp_base_type2 tx1' -> interp_flat_type interp_base_type2 tC2)
                      v1 v2,
                (forall a,
                    interp_flat_type_ivarf_R2b a v2
                    -> R (interpf interp_op1 (f a)) (g v2))
                -> interp_flat_type_ivarf_R2b v1 v2
                -> R (interpf interp_op1 (@transfer_var tx1 tx2 tC1 f v1))
                     (g v2)).

    Local Notation mapf_interp_cast
      := (@mapf_interp_cast
            base_type_code base_type_code interp_base_type2
            op op interp_op2 failv new_base_type
            transfer_op).
    Local Notation map_interp_cast
      := (@map_interp_cast
            base_type_code base_type_code interp_base_type2
            op op interp_op2 failv new_base_type
            transfer_op).

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

    Local Ltac fin_False :=
      lazymatch goal with
      | [ H : False |- _ ] => exfalso; assumption
      end.

    Local Ltac fin_t0 :=
      solve [ constructor; eauto
            | eauto
            | auto
            | hnf; auto ].

    Local Ltac fin_t1 :=
      solve [ lazymatch goal with
              | [ |- R' _ _ _ _ ] => eapply interp_flat_type_rel_pointwise2_hetero_flatten_binding_list2; eauto
              end ].

    Local Ltac handle_transfer_var_t :=
      match goal with
      | [ |- R (interpf _ (transfer_var _ _ _ _ _)) _ ]
        => apply R_transfer_var
      | [ |- R (interpf _ (transfer_var _ _ _ _ _)) (interpf ?interp_op (?e _)) ]
        => apply R_transfer_var with (g := fun v => interpf interp_op (e v))
      | [ |- R' ?t1 ?t2 (interpf _ (transfer_var ?tx1 ?tx2 ?tC1 (fun x => x) ?v1)) ?v2 ]
        => apply (R_transfer_var tx1 (Tbase _) tx2 tC1 (Tbase _) (fun x => x) (fun x => x))
      | [ H : _ |- R (interpf _ (mapf_interp_cast _ _ _)) (interpf _ _) ]
        => apply H
      end.

    Local Ltac handle_list_t :=
      match goal with
      | _ => progress cbv [LetIn.Let_In duplicate_types] in *
      | [ H : List.In _ (_ ++ _) |- _ ] => apply List.in_app_or in H
      | [ H : List.In _ (List.map _ _) |- _ ]
        => rewrite List.in_map_iff in H
      | _ => rewrite <- flatten_binding_list_flatten_binding_list2
      | [ H : appcontext[flatten_binding_list2] |- _ ]
        => rewrite <- flatten_binding_list_flatten_binding_list2 in H
      | [ H : context[flatten_binding_list (SmartVarfMap _ _) (SmartVarfMap _ _)] |- _ ]
        => rewrite flatten_binding_list_SmartVarfMap in H
      | [ H : context[flatten_binding_list2 (SmartVarfMap _ _) (SmartVarfMap _ _)] |- _ ]
        => rewrite flatten_binding_list2_SmartVarfMap in H
      | [ H : context[flatten_binding_list2 (SmartVarfMap _ _) _] |- _ ]
        => rewrite flatten_binding_list2_SmartVarfMap1 in H
      | [ H : context[flatten_binding_list2 _ (SmartVarfMap _ _)] |- _ ]
        => rewrite flatten_binding_list2_SmartVarfMap2 in H
      | _ => rewrite <- flatten_binding_list_flatten_binding_list2
      | _ => rewrite List.in_map_iff
      end.

    Local Ltac wff_t :=
      match goal with
      | [ |- wff _ _ _ ] => constructor
      | [ H : _ |- wff _ (mapf_interp_cast _ _ _) (mapf_interp_cast _ _ _) ]
        => eapply H; eauto; []; clear H
      | _ => solve [ eauto using wff_in_impl_Proper ]
      end.

    Local Ltac misc_t :=
      match goal with
      | [ H : _ |- R' _ _ (interpf _ ?x) ?y ]
        => is_var x; is_var y; apply H
      | [ |- exists _, _ ]
        => eexists (existT _ _ _)
      | [ |- _ /\ _ ] => split
      end.

    Local Ltac t_step :=
      first [ intro
            | fin_False
            | progress break_t
            | fin_t0
            | progress simpl in *
            | wff_t
            | handle_list_t
            | progress destruct_head' or
            | fin_t1
            | handle_transfer_var_t
            | misc_t ].

    Lemma interpf_mapf_interp_cast
          G
          (HG : forall t x y,
              List.In (existT _ t (x, y)%core) G
              -> R' (new_base_type t y) t
                    (interpf interp_op1
                             (transfer_var (Tbase _) (Tbase _) (Tbase _)
                                           (fun k => k) x))
                    y)
          {t1} e1 ebounds
          (Hwf : wff G e1 ebounds)
      : R (interpf interp_op1 (@mapf_interp_cast interp_base_type1 transfer_var t1 e1 t1 ebounds))
          (interpf interp_op2 ebounds).
    Proof. induction Hwf; repeat t_step. Qed.

    Local Hint Resolve interpf_mapf_interp_cast.

    Lemma interp_map_interp_cast
          {t1} e1 ebounds
          args2
          (Hwf : wf e1 ebounds)
      : forall v,
        R v args2
        -> R (interp interp_op1 (@map_interp_cast interp_base_type1 transfer_var t1 e1 t1 ebounds args2) v)
             (interp interp_op2 ebounds args2).
    Proof.
      destruct Hwf;
        repeat match goal with
               | _ => t_step
               | [ |- R (interpf _ (mapf_interp_cast _ _ _)) (interpf _ _) ]
                 => eapply interpf_mapf_interp_cast
               end.
    Qed.
  End with_var.

  Section gen.
    Context (transfer_var : forall ovar tx1 tx2 tC1
                                   (ivarf := fun t => @exprf base_type_code op ovar (Tbase t))
                                   (f : interp_flat_type ivarf tx1 -> exprf base_type_code op (var:=ovar) tC1)
                                   (v : interp_flat_type ivarf tx2),
                exprf base_type_code op (var:=ovar) tC1).
    Context (R_transfer_var
             : forall tx1 tx1' tx2 tC1 tC2
                      (f : interp_flat_type ivarf tx1 -> exprf base_type_code op tC1)
                      (g : interp_flat_type interp_base_type2 tx1' -> interp_flat_type interp_base_type2 tC2)
                      v1 v2,
                (forall a,
                    interp_flat_type_ivarf_R2b a v2
                    -> R (interpf interp_op1 (f a)) (g v2))
                -> interp_flat_type_ivarf_R2b v1 v2
                -> R (interpf interp_op1 (@transfer_var _ tx1 tx2 tC1 f v1))
                     (g v2)).

    Local Notation MapInterpCast
      := (@MapInterpCast
            base_type_code interp_base_type2
            op interp_op2 failv new_base_type
            transfer_op transfer_var).

    Lemma InterpMapInterpCast
          {t} e
          args
          (Hwf : Wf e)
      : forall v,
        R v args
        -> R (Interp interp_op1 (@MapInterpCast t e args) v)
             (Interp interp_op2 e args).
    Proof. apply interp_map_interp_cast; auto. Qed.
  End gen.
End language.
