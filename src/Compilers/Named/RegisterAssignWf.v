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
Require Import Crypto.Util.Tactics.SpecializeBy.

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

  Local Hint Resolve (@InName_dec InName InName_beq InName_bl InName_lb) : typeclass_instances.

  Local Notation InName_dec := (@InName_dec InName InName_beq InName_bl InName_lb).
  Local Notation register_reassignf := (@register_reassignf base_type_code op InName OutName InContext ReverseContext InName_beq).
  Local Notation register_reassign := (@register_reassign base_type_code op InName OutName InContext ReverseContext InName_beq).
  Local Notation lookupb_extend_helper := (@lookupb_extend_helper base_type_code InName OutName InContext ReverseContext InContextOk ReverseContextOk InName_beq base_type_code_dec OutName_dec InName_bl InName_lb).

  (*Local Ltac t :=
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
                   end ].*)

  (*Local Notation lookup_good ctxi ctxr
    := (forall t (n_in : InName) (n_out : OutName),
           lookupb ctxi n_in t = Some n_out
           <-> lookupb ctxr n_out t = Some n_in)
         (only parsing).

  Lemma lookup_good_extend
        (ctxi : InContext) (ctxr : ReverseContext) T ni no
        (H : lookup_good ctxi ctxr)
    : lookup_good (extend ctxi ni no) (extend (t:=T) ctxr no ni).
  Proof.
    intros t n_in n_out; specialize (H t n_in n_out).
    rewrite !(@lookupb_extend base_type_code _ InName _), !(@lookupb_extend base_type_code _ OutName _) by auto.
    induction T; [ | assumption | ].
    { simpl; unfold cast_if_eq; break_innermost_match; subst; simpl;
        eliminate_hprop_eq; simpl; split; try congruence.
      unfold cast_if_eq.
      repeat rewrite !(@find_Name_and_val_split base_type_code base_type_code_dec _ _ _ _ _ _ _ _ (lookupb _ _)).

      lazymatch goal with
      | [ |- context[dec ?P] ] => destruct (dec P)
      end.
      edestruct (dec (_ = _)); subst.
      repeat first [
                 | progress subst
                 | apply conj
                 | progress destruct_head' iff
                 | break_innermost_match_step
                 | congruence
                 | progress intros
                 | progress specialize_by_assumption ].
      Focus 4.
*)

  Section with_var.
    Context {var : base_type_code -> Type}
            {VarInContext : Context InName var}
            {VarOutContext : Context OutName var}
            {VarInContextOk : ContextOk VarInContext}
            {VarOutContextOk : ContextOk VarOutContext}.

    Local Notation lookup_good ctxi ctxr ctxi_var ctxr_var
      := (forall t (n_in : InName) (n_out : OutName) v,
             lookupb ctxi n_in t = Some n_out
             -> lookupb ctxr n_out t = Some n_in
             -> lookupb ctxi_var n_in t = Some v
             -> lookupb ctxr_var n_out t = None
             -> False)
           (only parsing).

    Lemma lookup_good_extend
          {ctxi : InContext} {ctxr : ReverseContext}
          {ctxi_var : VarInContext} {ctxr_var : VarOutContext}
          {T ni no v}
          (H : lookup_good ctxi ctxr ctxi_var ctxr_var)
      : lookup_good (extend ctxi ni no) (extend (t:=T) ctxr no ni)
                    (extend ctxi_var ni v) (extend ctxr_var no v).
    Proof.
      intros t n_in n_out v'; specialize (H t n_in n_out v').
      rewrite !(@lookupb_extend base_type_code _ InName _), !(@lookupb_extend base_type_code _ OutName _) by auto.
      repeat rewrite !(@find_Name_and_val_split base_type_code base_type_code_dec _ _ _ _ _ _ _ _ (lookupb _ _)).
      break_innermost_match; subst; eauto; try congruence.
      { clear H.
        induction T; [ | simpl; congruence | ].
        { simpl; unfold cast_if_eq; break_innermost_match; subst; simpl;
            eliminate_hprop_eq; simpl; congruence. }
        { simpl in *; destruct_head'_prod.
          repeat match goal with
                 | [ H : forall x : ?T, _, x' : ?T |- _ ] => specialize (H x')
                 end.
          simpl in *.
          repeat rewrite !(@find_Name_and_val_split base_type_code base_type_code_dec _ _ _ _ _ _ _ _ (find_Name_and_val _ _ _ _ _ _ _)).
          break_innermost_match; break_match_hyps; subst; eauto; try congruence;
            inversion_option; subst;
              intros;
              specialize_by_assumption; specialize_by reflexivity;
                repeat match goal with
                       | [ H : _ -> ?T -> _, H' : ?T |- _ ] => specialize (fun a => H a H')
                       | [ H : _ -> _ -> ?T -> _, H' : ?T |- _ ] => specialize (fun a b => H a b H')
                       | [ H : _ -> _ -> _ -> ?T -> _, H' : ?T |- _ ] => specialize (fun a b c => H a b c H')
                       | [ H : _ -> ?x = ?x -> _ |- _ ] => specialize (fun a => H a eq_refl)
                       | [ H : context[find_Name_and_val _ ?ndec ?t ?n ?N ?x ?default] |- _ ]
                         => rewrite (@find_Name_and_val_different base_type_code base_type_code_dec _ ndec _ t n _ N x default) in H by assumption
                       end.
          clear IHT2 Heqo.
          pose (@find_Name_and_val_different base_type_code base_type_code_dec InName _).
          match goal with
          end.
          SearchAbout find_Name None find_Name_and_val.


          simpl; unfold cast_if_eq; break_innermost_match; subst; simpl;
            eliminate_hprop_eq; simpl. congruence. }
      {
        eauto.
        unfold cast_if_eq.
      repeat rewrite !(@find_Name_and_val_split base_type_code base_type_code_dec _ _ _ _ _ _ _ _ (lookupb _ _)).
*)

    (* leaves the goal in a readable state (hopefully) *)
    Local Ltac t_careful :=
      repeat first [ progress intros
                   | progress unfold option_map in *
                   | progress simpl @register_reassignf in *
                   | progress simpl @prop_of_option in *
                   | progress autorewrite with push_prop_of_option in *
                   | progress destruct_head'_and
                   | progress inversion_option
                   | progress subst
                   | congruence
                   | assumption
                   | progress break_innermost_match_hyps
                   | progress break_innermost_match_step
                   | solve [ eauto ]
                   | match goal with
                     | [ H : InName_beq _ _ = true |- _ ] => apply InName_bl in H
                     | [ IH : forall ctxi ctxr new_names ctxi_var ctxr_var Hwf eout, _ -> register_reassignf _ _ _ _ = Some _ -> prop_of_option _,
                           Heq : register_reassignf _ _ _ _ = Some _ |- _ ]
                       => specialize (fun ctxi_var pf ctxr_var pf' => IH _ _ _ ctxi_var ctxr_var pf _ pf' Heq)
                     | [ IH : forall cv, prop_of_option (wff cv ?e) -> _, Hwf : prop_of_option (wff ?cv' ?e) |- _ ]
                       => specialize (IH cv' Hwf);
                          try match goal with
                              | [ H : forall t n_in n_out v, _ -> _ -> _ -> _ -> False |- _ ]
                                => specialize (IH _ H)
                              end
                     | [ IH : forall cv, prop_of_option (wff cv ?e) -> _, Hwf : forall x, prop_of_option (wff (@?cv' x) ?e) |- _ ]
                       => specialize (fun x => IH (cv' x) (Hwf x));
                          try match goal with
                              | [ H : forall t n_in n_out v, _ -> _ -> _ -> _ -> False |- _ ]
                                => specialize (IH _ H)
                              end
                     | [ |- _ /\ _ ] => split
                     end ].

    Lemma wff_register_reassignf
          ctxi ctxr t e new_names
          (ctxi_var : VarInContext)
          (ctxr_var : VarOutContext)
          eout
          (Hwf : prop_of_option (Named.wff ctxi_var e))
      : (forall t (n_in : InName) (n_out : OutName) v,
            lookupb ctxi n_in t = Some n_out
            -> lookupb ctxr n_out t = Some n_in
            -> lookupb ctxi_var n_in t = Some v
            -> lookupb ctxr_var n_out t = None
            -> False)
        (*(forall t (n_in : InName) (n_out : OutName),
            lookupb ctxi n_in t = Some n_out
            <-> lookupb ctxr n_out t = Some n_in)
        -> (forall t (n_in : InName) (n_out : OutName),
               lookupb ctxi n_in t = Some n_out
               -> lookupb ctxr n_out t = Some n_in
               -> lookupb ctxi_var n_in t = lookupb ctxr_var n_out t)*)
        -> @register_reassignf ctxi ctxr t e new_names = Some eout
        -> prop_of_option (Named.wff ctxr_var eout).
    Proof.
      revert ctxi ctxr new_names ctxi_var ctxr_var Hwf eout.
      induction e;
        try solve [ t_careful ].
      { t_careful.
        { eapply IHe2; clear IHe2 IHe1.

        break_innermost_match; simpl in *; eauto.
        break_innermost_match; simpl in *; eauto.
      try solve [ repeat first [ reflexivity
                     | assumption
                     | progress subst
                     | progress inversion_option
                     | progress simpl in *
                     | progress intros
                     | progress destruct_head'_and
                     | progress destruct_head'_or
                     | progress autorewrite with push_prop_of_option in *
                     | rewrite (@lookupb_extend base_type_code _ InName _)
                     | rewrite (@lookupb_extend base_type_code _ OutName _)
                     | progress intros
                     | progress unfold option_map in *
                     | solve [ eauto ]
                     | match goal with
                       | [ |- _ /\ _ ] => split
                       | [ H : forall t x y, _ = Some _ -> _ = Some _ -> _ = _,
                             H0 : _ = Some _, H1 : _ = Some _, H2 : _ = Some _, H3 : _ = None |- _ ]
                         => specialize (H _ _ _ H0 H1); rewrite H2, H3 in H; congruence
                       | [ H : _ |- prop_of_option (wff _ _) ]
                         => eapply H; [ .. | eassumption ]; [ solve [ eauto ] | .. ]
                       end
                     | break_innermost_match_step
                     | break_innermost_match_hyps_step
                     | match goal with
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
                       | [ H : _ |- _ ]
                         => first [ rewrite !(@lookupb_extend base_type_code _ InName _) in H
                                  | rewrite !(@lookupb_extend base_type_code _ OutName _) in H ]
                       end ] ].
      {
        all:eapply IHe2; clear IHe2 IHe1.
        Focus 2.
        Focus 3.
        specialize (IHe1 _ H).
        Focus 2.
          specialize (fun ctxi_var pf ctxr_var pf' => IHe1 _ _ _ ctxi_var ctxr_var pf _ pf' Heqo0).
          simpl in Hwf |- *.
          autorewrite with push_prop_of_option in *.
          destruct_head'_and.
          simpl in H1.
          repeat match goal with
                 end.
          cbv beta in *.
        Focus 3.
        3:repeat first [ reflexivity
                     | assumption
                     | progress subst
                     | progress inversion_option
                     | progress simpl in *
                     | progress intros
                     | progress destruct_head'_and
                     | progress destruct_head'_or
                     | progress autorewrite with push_prop_of_option in *
                     | rewrite (@lookupb_extend base_type_code _ InName _)
                     | rewrite (@lookupb_extend base_type_code _ OutName _)
                     | progress intros
                     | progress unfold option_map in *
                     | solve [ eauto ]
                     | match goal with
                       | [ H : InName_beq _ _ = true |- _ ] => apply InName_bl in H
                       | [ |- _ /\ _ ] => split
                       | [ H : forall t x y, _ = Some _ -> _ = Some _ -> _ = _,
                             H0 : _ = Some _, H1 : _ = Some _, H2 : _ = Some _, H3 : _ = None |- _ ]
                         => specialize (H _ _ _ H0 H1); rewrite H2, H3 in H; congruence
                       | [ H : _ |- prop_of_option (wff _ _) ]
                         => eapply H; [ .. | eassumption ]; [ solve [ eauto ] | .. ]
                       end
                     | break_innermost_match_step
                     | break_innermost_match_hyps_step
                     | match goal with
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
                       | [ H : _ |- _ ]
                         => first [ rewrite !(@lookupb_extend base_type_code _ InName _) in H
                                  | rewrite !(@lookupb_extend base_type_code _ OutName _) in H ]
                       end ].
        simpl.
          intros.
          { break_innermost_match_hyps; inversion_option; subst; simpl;
              match goal with
              | [ H : InName_beq _ _ = true |- _ ] => apply InName_bl in H
              end;
              subst; simpl in *; try tauto;
                break_innermost_match; simpl; try trivial.
            revert Heqo0 Heqo1 Heqo Heqo2.

            Focus 2.
            { simpl in *.
{      Info 0 repeat first [ reflexivity
                     | assumption
                     | progress subst
                     | progress inversion_option
                     | progress simpl in *
                     | progress intros
                     | progress destruct_head'_and
                     | progress destruct_head'_or
                     | progress autorewrite with push_prop_of_option in *
                     | rewrite (@lookupb_extend base_type_code _ InName _)
                     | rewrite (@lookupb_extend base_type_code _ OutName _)
                     | progress intros
                     | progress unfold option_map in *
                     | solve [ eauto ]
                     | match goal with
                       | [ H : InName_beq _ _ = true |- _ ] => apply InName_bl in H
                       | [ |- _ /\ _ ] => split
                       | [ H : forall t x y, _ = Some _ -> _ = Some _ -> _ = _,
                             H0 : _ = Some _, H1 : _ = Some _, H2 : _ = Some _, H3 : _ = None |- _ ]
                         => specialize (H _ _ _ H0 H1); rewrite H2, H3 in H; congruence
                       | [ H : _ |- prop_of_option (wff _ _) ]
                         => eapply H; [ .. | eassumption ]; [ solve [ eauto ] | .. ]
                       end
                     | break_innermost_match_step
                     | break_innermost_match_hyps_step
                     | match goal with
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
                       | [ H : _ |- _ ]
                         => first [ rewrite !(@lookupb_extend base_type_code _ InName _) in H
                                  | rewrite !(@lookupb_extend base_type_code _ OutName _) in H ]
                       end ].
      eauto.
      admit.
    Admitted.
    (*
      { repeat first [ reflexivity
                     | assumption
                     | progress subst
                     | progress inversion_option
                     | progress simpl in *
                     | progress intros
                     | progress destruct_head'_and
                     | progress destruct_head'_or
                     | progress autorewrite with push_prop_of_option in *
                     | rewrite (@lookupb_extend base_type_code _ InName _)
                     | rewrite (@lookupb_extend base_type_code _ OutName _)
                     | progress intros
                     | progress unfold option_map in *
                     | solve [ eapply find_Name_and_val_same_oval; eauto ]
                     | match goal with
                       | [ H : InName_beq _ _ = true |- _ ] => apply InName_bl in H
                       | [ |- _ /\ _ ] => split
                       | [ H : forall t x y, _ = Some _ -> _ = Some _ -> _ = _,
                             H0 : _ = Some _, H1 : _ = Some _, H2 : _ = Some _, H3 : _ = None |- _ ]
                         => specialize (H _ _ _ H0 H1); rewrite H2, H3 in H; congruence
                       | [ H : _ |- prop_of_option (wff _ _) ]
                         => eapply H; [ .. | eassumption ]; [ solve [ eauto ] | .. ]
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
                       (*| [ H : _ |- _ ]
                         => first [ rewrite !(@lookupb_extend base_type_code _ InName _) in H
                                  | rewrite !(@lookupb_extend base_type_code _ OutName _) in H ]*)
                       end
                     | break_innermost_match_step
                     | break_innermost_match_hyps_step ].
        Focus 2.
        { match goal with
          | [ H : _ = Some _, H' : _ = Some _ |- _ ]
            => let c := open_constr:(find_Name_and_val_same_val InName_bl InName_lb H) in
               pose proof c
          end. *)

    Local Notation ctx_var_good ctxi ctxr ctxi_var ctxr_var
      := (forall t (n_in : InName) (n_out : OutName),
             lookupb ctxi n_in t = Some n_out
             -> lookupb ctxr n_out t = Some n_in
             -> lookupb ctxi_var n_in t = lookupb ctxr_var n_out t)
           (only parsing).
    (*Lemma lookup_good_extend
          (ctxi : InContext) (ctxr : ReverseContext) T i i0
          (H : lookup_good ctxi ctxr)
      : lookup_good (extend ctxi i i0) (extend (t:=T) ctxr i0 i).
    Proof.
      intros t n_in n_out; specialize (H t n_in n_out).
      rewrite !(@lookupb_extend base_type_code _ InName _), !(@lookupb_extend base_type_code _ OutName _) by auto.
      induction T; [ | assumption | ].
      { simpl; unfold cast_if_eq; break_innermost_match; subst; simpl;
          eliminate_hprop_eq; simpl; split; try congruence.
        unfold cast_if_eq.
      repeat rewrite !(@find_Name_and_val_split base_type_code base_type_code_dec _ _ _ _ _ _ _ _ (lookupb _ _)).

      lazymatch goal with
      | [ |- context[dec ?P] ] => destruct (dec P)
      end.
      edestruct (dec (_ = _)); subst.
      repeat first [
                   | progress subst
                   | apply conj
                   | progress destruct_head' iff
                   | break_innermost_match_step
                   | congruence
                   | progress intros
                   | progress specialize_by_assumption ].
      Focus 4.

    Lemma ctx_var_good_extend
          (ctxi : InContext) (ctxr : ReverseContext) T i i0 v
          (ctxi_var : VarInContext)
          (ctxr_var : VarOutContext)
          (Hg : lookup_good ctxi ctxr)
          (H : ctx_var_good ctxi ctxr ctxi_var ctxr_var)
      : ctx_var_good (extend ctxi i i0) (extend ctxr i0 i) (extend ctxi_var i v) (extend (t:=T) ctxr_var i0 v).
    Proof.
      intros t n_in n_out; specialize (H t n_in n_out).
      rewrite !(@lookupb_extend base_type_code _ InName _), !(@lookupb_extend base_type_code _ OutName _) by auto.
      repeat first [ rewrite !(@find_Name_and_val_split base_type_code base_type_code_dec _ _ _ _ _ _ _ _ (lookupb _ _))
                   | congruence
                   | progress subst
                   | break_innermost_match_step
                   | progress intros
                   | progress specialize_by_assumption ].
      Focus 2.

      Focus 2.
      rewrite !(@find_Name_and_val_split base_type_code base_type_code_dec InName InName_dec _ _ _ _ _ _ (lookupb _ _)).
      rewrite
      rewrite (lookupb_extend _).

      forall (t : base_type_code) (n_in : InName) (n_out : OutName),
  lookupb (extend ctxi i i0) n_in = Some n_out ->
  lookupb (extend ctxr i0 i) n_out = Some n_in ->
  lookupb (extend ctxi_var i ?v) n_in = lookupb (extend ctxr_var i0 v) n_out*)

    Lemma wf_register_reassign
          ctxi ctxr t e new_names
          (ctxi_var : VarInContext)
          (ctxr_var : VarOutContext)
          eout
          (Hwf : Named.wf ctxi_var e)
      : (*(forall t (n_in : InName) (n_out : OutName),
            lookupb ctxi n_in t = Some n_out
            <-> lookupb ctxr n_out t = Some n_in)
        -> (forall t (n_in : InName) (n_out : OutName),
               lookupb ctxi n_in t = Some n_out
               -> lookupb ctxr n_out t = Some n_in
               -> lookupb ctxi_var n_in t = lookupb ctxr_var n_out t)
        ->*) @register_reassign ctxi ctxr t e new_names = Some eout
        -> Named.wf ctxr_var eout.
    Proof.
      destruct e; unfold Named.wf, register_reassign, option_map in *.
      break_innermost_match; try congruence.
      intros Hlookup_ir Hlookup_var; intros; inversion_option; subst; simpl in *.
      eapply wff_register_reassignf; [ .. | eassumption ]; [ solve [ eauto ] | .. ].

      all:intros *;
        rewrite !(@lookupb_extend base_type_code _ InName _), !(@lookupb_extend base_type_code _ OutName _) by auto.
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
