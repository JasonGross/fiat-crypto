Require Import Coq.Bool.Sumbool.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.WfInversion.
Require Import Crypto.Compilers.WfProofs.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.MapBaseType.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Bool.

Section language.
  Context {base_type_code1 base_type_code2 : Type}
          {op1 : flat_type base_type_code1 -> flat_type base_type_code1 -> Type}
          {op2 : flat_type base_type_code2 -> flat_type base_type_code2 -> Type}
          (f_base : base_type_code1 -> base_type_code2)
          (f_op : forall s d,
              op1 s d
              -> option (op2 (lift_flat_type f_base s) (lift_flat_type f_base d)))
          (check_base_type : base_type_code1 -> bool).

  Section with_interp_cast.
    Context {interp_base_type1 : base_type_code1 -> Type}
            {interp_base_type2 : base_type_code2 -> Type}
            {interp_op1 : forall s d, op1 s d -> interp_flat_type interp_base_type1 s -> interp_flat_type interp_base_type1 d}
            {interp_op2 : forall s d, op2 s d -> interp_flat_type interp_base_type2 s -> interp_flat_type interp_base_type2 d}
            (cast_backb: forall t, interp_base_type2 (f_base t) -> interp_base_type1 t)
            (castb : forall t, interp_base_type1 t -> interp_base_type2 (f_base t))
            (Hcast_backb_castb
             : forall t x, check_base_type t = true
                           -> x = cast_backb t (castb t x)).
    Let cast_back : forall t, interp_flat_type interp_base_type2 (lift_flat_type f_base t) -> interp_flat_type interp_base_type1 t
      := fun t => untransfer_interp_flat_type f_base cast_backb.
    Context (f_op_cast_back
             : forall s d opc1 opc2 args2,
                f_op s d opc1 = Some opc2
                -> interp_op1 _ _ opc1 (cast_back _ args2)
                   = cast_back _ (interp_op2 _ _ opc2 args2)).

    Local Hint Constructors wf wff or.

    Local Notation mapf_base_type :=
      (@mapf_base_type base_type_code1 base_type_code2 op1 op2 f_base f_op).
    Local Notation map_base_type :=
      (@map_base_type base_type_code1 base_type_code2 op1 op2 f_base f_op).

    Section with_var.
      Context {var : base_type_code1 -> Type}
              {val : forall t, var t}
              (failb : forall t, exprf _ op2 (var:=interp_base_type2) (Tbase t)).

      Lemma interpf_mapf_base_type G {t}
            (e : exprf base_type_code1 op1 (var:=interp_base_type1) t)
            (eb : exprf base_type_code1 op1 (var:=var) t)
            (Hwf : wff G e eb)
            (Hb : check_mapf_base_type_gen _ f_op check_base_type val eb = true)
        : interpf interp_op1 e
          = cast_back _ (interpf interp_op2 (mapf_base_type castb cast_backb failb e)).
      Proof using Hcast_backb_castb f_op_cast_back.
        induction Hwf;
          repeat first [ progress simpl in *
                       | reflexivity
                       | progress split_andb
                       | progress specialize_by_assumption
                       | solve [ eauto ]
                       | break_innermost_match_step
                       | erewrite <- f_op_cast_back by eassumption
                       | progress cbv [LetIn.Let_In cast_back] in *
                       | congruence
                       | match goal with
                         | [ H : context[interpf _ _ = untransfer_interp_flat_type _ cast_backb _] |- _ ]
                           => erewrite <- H by eassumption
                         end ].
      Qed.

      Lemma interp_map_base_type {t}
            (e : expr base_type_code1 op1 (var:=interp_base_type1) t)
            (eb : expr base_type_code1 op1 (var:=var) t)
            (Hwf : wf e eb)
            (Hb : check_map_base_type_gen _ f_op check_base_type val eb = true)
        : forall x,
          interp interp_op1 e (cast_back _ x)
          = cast_back _ (interp interp_op2 (map_base_type castb cast_backb failb e) x).
      Proof using Hcast_backb_castb f_op_cast_back.
        destruct Hwf; simpl in *; intros; eapply interpf_mapf_base_type; eauto.
      Qed.
    End with_var.
  End with_interp_cast.

  Section with_interp_cast_id.
    Context {interp_base_type1 : base_type_code1 -> Type}
            {interp_base_type2 : base_type_code2 -> Type}
            {interp_op1 : forall s d, op1 s d -> interp_flat_type interp_base_type1 s -> interp_flat_type interp_base_type1 d}
            {interp_op2 : forall s d, op2 s d -> interp_flat_type interp_base_type2 s -> interp_flat_type interp_base_type2 d}
            (cast_backb: forall t, interp_base_type2 (f_base t) -> interp_base_type1 t)
            (castb : forall t, interp_base_type1 t -> interp_base_type2 (f_base t))
            (Hcast_backb_castb
             : forall t x, check_base_type t = true
                           -> x = cast_backb t (castb t x)).
    Let cast_back : forall t, interp_flat_type interp_base_type2 (lift_flat_type f_base t) -> interp_flat_type interp_base_type1 t
      := fun t => untransfer_interp_flat_type f_base cast_backb.
    Context (f_op_cast_back
             : forall s d opc1 opc2 args2,
                f_op s d opc1 = Some opc2
                -> interp_op1 _ _ opc1 (cast_back _ args2)
                   = cast_back _ (interp_op2 _ _ opc2 args2)).

    Local Hint Constructors wf wff or.

    Local Notation mapf_base_type :=
      (@mapf_base_type base_type_code1 base_type_code2 op1 op2 f_base f_op).
    Local Notation map_base_type :=
      (@map_base_type base_type_code1 base_type_code2 op1 op2 f_base f_op).

    Section with_var.
      Context {var : base_type_code1 -> Type}
              {val : forall t, var t}
              (failb : forall t, exprf _ op2 (var:=interp_base_type2) (Tbase t)).

      Lemma interpf_mapf_base_type_id G G' {t}
            (e : exprf base_type_code1 op1 (var:=interp_base_type1) t)
            (e' : exprf base_type_code1 op1 (var:=fun t => interp_base_type2 (f_base t)) t)
            (eb : exprf base_type_code1 op1 (var:=var) t)
            (Hwf : wff G e eb)
            (Hwf' : wff G' e e')
            (HG' : forall t x v,
                List.In
                  (existT _ t (x, v)) G'
                -> x = cast_backb t v)
            (Hb : check_mapf_base_type_gen _ f_op check_base_type val eb = true)
        : interpf interp_op1 e
          = cast_back
              _
              (interpf
                 interp_op2
                 (mapf_base_type
                    (var1:=fun t => interp_base_type2 (f_base t))
                    (var2:=interp_base_type2)
                    (fun _ x => x) (fun _ x => x) failb e')).
      Proof using Hcast_backb_castb f_op_cast_back.
        revert dependent G'; revert dependent e'; induction Hwf; intros; invert_expr; intros; inversion_wf_constr;
          repeat first [ progress simpl in *
                       | reflexivity
                       | exfalso; assumption
                       | progress subst
                       | progress inversion_option
                       | progress inversion_sigma
                       | progress inversion_prod
                       | progress destruct_head'_sig
                       | progress destruct_head'_and
                       | progress split_andb
                       | progress specialize_by_assumption
                       | erewrite <- f_op_cast_back by eassumption
                       | solve [ eauto ]
                       | break_innermost_match_step
                       | break_innermost_match_hyps_step
                       | progress intros
                       | progress inversion_wf_constr
                       | congruence
                       | progress cbv [LetIn.Let_In invert_Op invert_LetIn cast_back] in *
                       | progress inversion_wf_one_constr
                       | match goal with
                         | [ H : context[interpf _ _ = untransfer_interp_flat_type _ cast_backb _] |- _ ]
                           => erewrite <- H by eassumption
                         end ].
        { match goal with
          | [ H : context[interpf _ _ = untransfer_interp_flat_type _ cast_backb _] |- _ ]
            => erewrite <- H; [ reflexivity | eassumption | eauto | ]
          end.
          repeat first [ setoid_rewrite List.in_app_iff ].
          intros; eauto; destruct_head'_or; eauto.
          move x0 at bottom.
          move e1 at bottom.
          setoid_rewrite <- IHHwf in H5.
          2:eassumption.
          Focus 2.
          apply IH
        erewrite <- H0.
        2:eassumption.


        { match goal with
          | [ H : wff

        setoid_rewrite  <- IHHwf.
        { exfalso; clear -Hwf'.
          lazymatch type of Hwf' with
          | wff _ ?x ?y
            => is_expr_constructor TT.
let postprocess H :=
      (cbv [wff_code wf_code] in H;
       simpl in H;
       try match type of H with
           | True => clear H
           | False => exfalso; exact H
           end) in
            apply wff_encode in Hwf'; postprocess Hwf'.
          | [ H : wff _ ?x ?y |- _ ]
            => apply wguard_tac x y;
       apply wff_encode in H; postprocess H

                                          inversion_wf_step_constr.
          repeat first [ progress simpl in *
                       | reflexivity
                       | progress split_andb
                       | progress specialize_by_assumption
                       | solve [ eauto ]
                       | break_innermost_match_step
                       | erewrite <- f_op_cast_back by eassumption
                       | progress cbv [LetIn.Let_In cast_back] in *
                       | congruence
                       | match goal with
                         | [ H : context[interpf _ _ = untransfer_interp_flat_type _ cast_backb _] |- _ ]
                           => erewrite <- H by eassumption
                         | [ |- tt = ?x ] => destruct x; reflexivity
                         end ].

        simpl.
      Qed.

      Lemma interp_map_base_type {t}
            (e : expr base_type_code1 op1 (var:=interp_base_type1) t)
            (eb : expr base_type_code1 op1 (var:=var) t)
            (Hwf : wf e eb)
            (Hb : check_map_base_type_gen _ f_op check_base_type val eb = true)
        : forall x,
          interp interp_op1 e (cast_back _ x)
          = cast_back _ (interp interp_op2 (map_base_type castb cast_backb failb e) x).
      Proof using Hcast_backb_castb f_op_cast_back.
        destruct Hwf; simpl in *; intros; eapply interpf_mapf_base_type; eauto.
      Qed.
    End with_var.
  End with_interp_cast.

  Section with_interp_cast2.
    Context {interp_base_type1 : base_type_code1 -> Type}
            {interp_base_type2 : base_type_code2 -> Type}
            {interp_op1 : forall s d, op1 s d -> interp_flat_type interp_base_type1 s -> interp_flat_type interp_base_type1 d}
            {interp_op2 : forall s d, op2 s d -> interp_flat_type interp_base_type2 s -> interp_flat_type interp_base_type2 d}
            (cast_backb: forall t, interp_base_type2 (f_base t) -> interp_base_type1 t).
    Let cast_back : forall t, interp_flat_type interp_base_type2 (lift_flat_type f_base t) -> interp_flat_type interp_base_type1 t
      := fun t => untransfer_interp_flat_type f_base cast_backb.
    Context (f_op_cast_back
             : forall s d opc1 opc2 args2,
                f_op s d opc1 = Some opc2
                -> interp_op1 _ _ opc1 (cast_back _ args2)
                   = cast_back _ (interp_op2 _ _ opc2 args2)).

    Lemma InterpMapBaseType
          (failb : forall var t, exprf _ op2 (var:=var) (Tbase t))
          {t} (e : Expr base_type_code1 op1 t)
          (Hwf : Wf e)
          (Hb : check_map_base_type _ f_op check_base_type (e _) = true)
      : forall x, Interp interp_op1 e (cast_back _ x)
                  = cast_back _ (Interp interp_op2 (MapBaseType f_base f_op failb e) x).
    Proof using Type.
      cbv [Interp MapBaseType cast_back check_map_base_type] in *; intros.
      match goal with
      | [ H : check_map_base_type_gen _ _ _ _ (e ?var0) = true |- ?LHS = ?RHS ]
        => lazymatch LHS with
           | context[e ?var1]
             => lazymatch RHS with
                | context[e ?var2]
                  => pose proof (Hwf var1 var2) as Hwf';
                       pose proof (Hwf var1 var0) as Hwf0;
                       move Hwf' at top;
                       move Hwf at top;
                       generalize dependent (e var0);
                       generalize dependent (e var2); intros e2 Hwf';
                       generalize dependent (e var1); intros e1 Hwf'
                end
           end
      end.
      destruct Hwf'; simpl; intros; inversion_wf_step.
      invert_expr; intros; clear Hwf; simpl in *.
      repeat match goal with
             | [ Hwf : forall x0 x1, wff _ _ _
                                     |- interpf _ (?e0 ?x) = ?f (interpf _ (?g (?e' ?y))) ]
               => specialize (Hwf x y)
             end.


      unshelve erewrite interp_map_base_type by (eassumption || eauto); [ apply failb | ].
      apply f_equal.

    instantiate (1:=failb _).
    Focus 2.
    cbv [check_map_base_type] in *.
    eassumption.

    intros var1 var2; apply wf_map_base_type; eauto.
  Qed.
End language.

Hint Resolve @Wf_MapBaseType : wf.
