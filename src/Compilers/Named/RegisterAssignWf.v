Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.Named.Wf.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.ContextProperties.
Require Import Crypto.Compilers.Named.RegisterAssign.
Require Import Crypto.Compilers.Named.RegisterAssignInterp.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.

Local Open Scope nexpr_scope.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {InName OutName : Type}
          {InContext : Context InName (fun _ : base_type_code => OutName)}
          {ReverseContext : Context OutName (fun _ : base_type_code => InName)}
          {InContextOk : ContextOk InContext}
          {ReverseContextOk : ContextOk ReverseContext}
          {InName_beq : InName -> InName -> bool}
          {base_type_code_dec : DecidableRel (@eq base_type_code)}
          {OutName_dec : DecidableRel (@eq OutName)}
          (InName_bl : forall n1 n2, InName_beq n1 n2 = true -> n1 = n2)
          (InName_lb : forall n1 n2, n1 = n2 -> InName_beq n1 n2 = true).

  Local Instance InName_dec : DecidableRel (@eq InName)
    := dec_rel_of_bool_dec_rel InName_beq InName_bl InName_lb.

  Local Notation register_reassignf := (@register_reassignf base_type_code op InName OutName InContext ReverseContext InName_beq).
  Local Notation register_reassign := (@register_reassign base_type_code op InName OutName InContext ReverseContext InName_beq).

  Local Ltac t :=
    repeat first [ reflexivity
                 | assumption
                 | progress subst
                 | progress inversion_option
                 | progress simpl in *
                 | progress intros *
                 | progress intros
                 | progress destruct_head'_and
                 | progress destruct_head'_or
                 | progress autorewrite with push_prop_of_option in *
                 | rewrite (@lookupb_extend base_type_code _ InName _)
                 | rewrite (@lookupb_extend base_type_code _ OutName _)
                 | match goal with
                   | [ H : InName_beq _ _ = true |- _ ] => apply InName_bl in H
                   | [ H : _ = Some ?v1, H' : _ = Some ?v2 |- _ ]
                     => is_var v1; is_var v2;
                        assert (v1 = v2) by eauto; progress subst
                   | [ H : lookupb (extend _ _ _) _ = Some _, H' : lookupb (extend _ _ _) _ = Some _ |- _ ]
                     => pose proof (lookupb_extend_helper H H'); clear H H'
                   | [ H : find_Name_and_val _ _ _ _ _ _ ?x = _ |- _ ]
                     => lazymatch x with
                        | None => fail
                        | _ => rewrite find_Name_and_val_split in H
                        end
                   | [ |- context[@find_Name_and_val ?base_type_code ?Name ?base_type_code_dec ?Name_dec ?var' ?t ?n ?T ?N ?V ?default] ]
                     => lazymatch default with
                        | None => fail
                        | _ => rewrite (@find_Name_and_val_split base_type_code base_type_code_dec Name Name_dec var' t n T N V default)
                        end
                   | [ H : forall t n1 n2, lookupb _ n1 = Some n2 -> lookupb _ n2 = Some n1 -> lookupb _ _ = lookupb _ _,
                         H0 : lookupb _ _ = Some _, H1 : lookupb _ _ = Some _, H2 : lookupb _ _ = Some _, H3 : lookupb _ _ = None |- _ ]
                     => specialize (H _ _ _ H0 H1); rewrite H2, H3 in H; congruence
                   | [ H : _ |- _ ]
                     => first [ rewrite (@lookupb_remove base_type_code InName _) in H
                              | rewrite (@lookupb_remove base_type_code OutName _) in H
                              | rewrite (@lookupb_extend base_type_code _ InName _) in H
                              | rewrite (@lookupb_extend base_type_code _ OutName _) in H
                              | rewrite find_Name_and_val_different in H by assumption ]
                   | [ |- _ /\ _ ] => split
                   | [ |- _ <-> _ ] => split
                   end
                 | break_innermost_match_step
                 | break_innermost_match_hyps_step
                 | progress cbv [option_map LetIn.Let_In] in *
                 | solve [ eauto using find_Name_and_val_same_oval | eapply find_Name_and_val_same_oval; eauto ]
                 | match goal with
                   | [ H : _ |- prop_of_option (wff _ ?v) ]
                     => is_var v;
                        eapply H; [ solve [ eauto ] | | | eassumption ]; clear H
                   end ].

  Section with_var.
    Context {var : base_type_code -> Type}
            {VarInContext : Context InName var}
            {VarOutContext : Context OutName var}
            {VarInContextOk : ContextOk VarInContext}
            {VarOutContextOk : ContextOk VarOutContext}.

    Lemma wff_register_reassignf
          ctxi ctxr t e new_names
          (ctxi_var : VarInContext)
          (ctxr_var : VarOutContext)
          eout
          (Hwf : prop_of_option (Named.wff ctxi_var e))
      : (forall t (n_in : InName) (n_out : OutName),
            lookupb ctxi n_in t = Some n_out
            <-> lookupb ctxr n_out t = Some n_in)
        -> (forall t (n_in : InName) (n_out : OutName),
               lookupb ctxi n_in t = Some n_out
               -> lookupb ctxr n_out t = Some n_in
               -> lookupb ctxi_var n_in t = lookupb ctxr_var n_out t)
        -> @register_reassignf ctxi ctxr t e new_names = Some eout
        -> prop_of_option (Named.wff ctxr_var eout).
    Proof.
      revert ctxi ctxr new_names ctxi_var ctxr_var Hwf eout.
      induction e; t.
    Admitted.

    Lemma wf_register_reassign
          ctxi ctxr t e new_names
          (ctxi_var : VarInContext)
          (ctxr_var : VarOutContext)
          eout
          (Hwf : Named.wf ctxi_var e)
      : (forall t (n_in : InName) (n_out : OutName),
            lookupb ctxi n_in t = Some n_out
            <-> lookupb ctxr n_out t = Some n_in)
        -> (forall t (n_in : InName) (n_out : OutName),
               lookupb ctxi n_in t = Some n_out
               -> lookupb ctxr n_out t = Some n_in
               -> lookupb ctxi_var n_in t = lookupb ctxr_var n_out t)
        -> @register_reassign ctxi ctxr t e new_names = Some eout
        -> Named.wf ctxr_var eout.
    Proof.
      destruct e; unfold Named.wf, register_reassign, option_map in *.
      break_innermost_match; try congruence.
      intros Hlookup_ir Hlookup_var; intros; inversion_option; subst; simpl in *.
      eapply wff_register_reassignf; [ | | | eassumption ]; [ solve [ eauto ] | .. ].
      all:intros *;
        rewrite !(@lookupb_extend base_type_code _ InName _), !(@lookupb_extend base_type_code _ OutName _).
    Admitted.
  End with_var.

  Lemma Wf_register_reassign
        (InContext_var : forall var, Context InName var)
        (OutContext_var : forall var, Context OutName var)
        (InContext_varOk : forall var, ContextOk (InContext_var var))
        (OutContext_varOk : forall var, ContextOk (OutContext_var var))
        t e new_names
        eout
        (Hwf : Named.Wf InContext_var e)
    : @register_reassign empty empty t e new_names = Some eout
      -> Named.Wf OutContext_var eout.
  Proof.
    intros H ?; revert H.
    eapply wf_register_reassign; [ eapply Hwf | .. ];
      intros *;
      rewrite !lookupb_empty by eassumption; try split; congruence.
  Qed.
End language.

Hint Resolve wf_register_reassign Wf_register_reassign : wf.
