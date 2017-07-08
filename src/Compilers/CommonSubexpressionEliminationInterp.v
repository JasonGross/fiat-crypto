(** * Common Subexpression Elimination for PHOAS Syntax *)
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.AListContext.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.ContextProperties.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Equality.
Require Import Crypto.Compilers.WfInversion.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.WfProofs.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.CommonSubexpressionElimination.
Require Import Crypto.Compilers.CommonSubexpressionEliminationDenote.
(*Require Import Crypto.Compilers.CommonSubexpressionEliminationWf.*)
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.HProp.

Section symbolic.
  Context (base_type_code : Type)
          (op_code : Type)
          (base_type_code_beq : base_type_code -> base_type_code -> bool)
          (op_code_beq : op_code -> op_code -> bool)
          (base_type_code_bl : forall x y, base_type_code_beq x y = true -> x = y)
          (base_type_code_lb : forall x y, x = y -> base_type_code_beq x y = true)
          (op_code_bl : forall x y, op_code_beq x y = true -> x = y)
          (op_code_lb : forall x y, x = y -> op_code_beq x y = true)
          (interp_base_type : base_type_code -> Type)
          (op : flat_type base_type_code -> flat_type base_type_code -> Type)
          (interp_op : forall s d (opc : op s d), interp_flat_type interp_base_type s -> interp_flat_type interp_base_type d)
          (symbolize_op : forall s d, op s d -> op_code)
          (denote_op : forall s d, op_code -> option (op s d)).
  Local Notation symbolic_expr := (symbolic_expr base_type_code op_code).
  Context (normalize_symbolic_op_arguments : op_code -> symbolic_expr -> symbolic_expr)
          (inline_symbolic_expr_in_lookup : bool).

  Local Notation symbolic_expr_beq := (@symbolic_expr_beq base_type_code op_code base_type_code_beq op_code_beq).
  Local Notation symbolic_expr_lb := (@internal_symbolic_expr_dec_lb base_type_code op_code base_type_code_beq op_code_beq base_type_code_lb op_code_lb).
  Local Notation symbolic_expr_bl := (@internal_symbolic_expr_dec_bl base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op_code_bl).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation interp_type := (interp_type interp_base_type).
  Local Notation interp_flat_type_gen := interp_flat_type.
  Local Notation interp_flat_type := (interp_flat_type interp_base_type).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).

  Local Notation symbolicify_smart_var := (@symbolicify_smart_var base_type_code op_code).
  Local Notation symbolize_exprf := (@symbolize_exprf base_type_code op_code op symbolize_op).
  Local Notation csef := (@csef base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op symbolize_op normalize_symbolic_op_arguments inline_symbolic_expr_in_lookup).
  Local Notation cse := (@cse base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op symbolize_op normalize_symbolic_op_arguments inline_symbolic_expr_in_lookup).
  Local Notation CSE := (@CSE base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op symbolize_op normalize_symbolic_op_arguments inline_symbolic_expr_in_lookup).
  Local Notation SymbolicExprContext := (@SymbolicExprContext base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl).
  Local Notation SymbolicExprContextOk := (@SymbolicExprContextOk base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl base_type_code_lb op_code_bl op_code_lb).
  Local Notation prepend_prefix := (@prepend_prefix base_type_code op).

  Local Notation denote_symbolic_expr := (@denote_symbolic_expr base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op denote_op interp_base_type interp_op).

  Local Notation norm_symbolize_exprf := (@norm_symbolize_exprf base_type_code op_code op symbolize_op normalize_symbolic_op_arguments).

  Context (denote_symbolic_expr_normalize
           : forall t m e, denote_symbolic_expr m t (symbolic_expr_normalize base_type_code op_code normalize_symbolic_op_arguments e) = denote_symbolic_expr m t e).
  Context (denote_symbolize_op
           : forall s d opc, denote_op s d (symbolize_op s d opc) = Some opc).

  Local Instance base_type_code_dec : DecidableRel (@eq base_type_code)
    := dec_rel_of_bool_dec_rel base_type_code_beq base_type_code_bl base_type_code_lb.
  Local Instance op_code_dec : DecidableRel (@eq op_code)
    := dec_rel_of_bool_dec_rel op_code_beq op_code_bl op_code_lb.

  Lemma interpf_flatten_binding_list T t x y v s
        (H : List.In (existT _ t (x, y)) (flatten_binding_list (var2:=interp_base_type) (t:=T) (symbolicify_smart_var v s) v))
    : fst x = y.
  Proof.
    revert dependent s; induction T;
      repeat first [ progress simpl in *
                   | reflexivity
                   | tauto
                   | progress destruct_head or
                   | progress inversion_sigma
                   | progress inversion_prod
                   | progress subst
                   | rewrite List.in_app_iff in *
                   | progress intros
                   | solve [ eauto ] ].
  Qed.

  Lemma denote_symbolic_expr_flatten_binding_list T t x y v s m
        (Hm : forall t sv v,
            lookupb m sv = Some v
            -> denote_symbolic_expr m t sv = Some v)
        (Heq : denote_symbolic_expr m T s = Some v)
        (H : List.In (existT _ t (x, y)) (flatten_binding_list (var2:=interp_base_type) (t:=T) (symbolicify_smart_var v s) v))
    : denote_symbolic_expr m (Tbase t) (snd x) = Some y.
  Proof.
    revert dependent s; induction T;
      try solve [ repeat first [ progress simpl in *
                               | reflexivity
                               | tauto
                               | progress destruct_head or
                               | progress inversion_sigma
                               | progress inversion_prod
                               | progress inversion_option
                               | progress subst
                               | rewrite List.in_app_iff in *
                               | progress intros
                               | progress cbn [fst snd projT1 projT2] in *
                               | solve [ eauto ]
                               | break_innermost_match_hyps_step
                               | unfold var_cast in *;
                                 break_innermost_match_hyps;
                                 [ lazymatch goal with
                                   | [ H : context[match eq_trans ?p (eq_sym ?q) with _ => _ end] |- _ ]
                                     => revert H; generalize p; generalize (eq_sym q); intros
                                   end
                                 | discriminate.. ]
                               | progress eliminate_hprop_eq
                               | progress destruct_head'_prod
                               | progress destruct_head'_sigT ] ].
    { intro s;
        specialize (IHT1 (fst v) (SFst T1 T2 s));
        specialize (IHT2 (snd v) (SSnd T1 T2 s)).
      repeat first [ progress cbn [denote_symbolic_expr option_map] in *
                   | progress break_innermost_match_hyps_step
                   | discriminate
                   | match goal with
                     | [ H : context[flat_type_beq _ _ ?x ?x] |- _ ]
                       => setoid_rewrite (flat_type_dec_lb _ _ base_type_code_lb x x eq_refl) in H
                     | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
                     end
                   | progress specialize_by reflexivity
                   | progress intros
                   | progress simpl in *
                   | rewrite in_app_iff in *
                   | progress destruct_head'_or
                   | solve [ eauto ] ]. }
  Qed.

  (*Lemma interpf_symbolize_exprf_injective
        s
    : forall G0 G1 t e0 e1 e0' e1'
             (HG0 : forall t x y, In (existT _ t (x, y)) G0 -> fst x = y)
             (HG1 : forall t x y, In (existT _ t (x, y)) G1 -> fst x = y)
             (Hwf0 : wff G0 (t:=t) e0 e0')
             (Hwf1 : wff G1 (t:=t) e1 e1')
             (Hs0 : symbolize_exprf e0 = Some s)
             (Hs1 : symbolize_exprf e1 = Some s),
      interpf interp_op e0' = interpf interp_op e1'.
  Proof.
    induction s; intros;
      destruct Hwf0;
      try (invert_one_expr e1; break_innermost_match; try exact I; intros);
      try (invert_one_expr e1'; break_innermost_match; try exact I; intros);
      try solve [ repeat first [ reflexivity
                               | progress subst
                               | progress destruct_head'_sig
                               | progress destruct_head'_and
                               | progress destruct_head'_prod
                               | progress inversion_option
                               | congruence
                               | progress simpl in *
                               | progress unfold option_map in *
                               | progress inversion_wf_constr
                               | break_innermost_match_hyps_step
                               | match goal with
                                 | [ HG : forall t x y, In _ ?G -> fst x = y, H : In _ ?G |- _ ]
                                   => pose proof (HG _ _ _ H); progress subst
                                 end ] ].
    Focus 3.
    { simpl in *.
    Focus 3.
    try reflexivity;
        simpl in *.
      inversion_expr.
        .
      inversion_wf.
    move s at top; reverse.
                ->

   *)

  Lemma denote_symbolic_expr_symbolize_exprf {t G e e' s}
        (HG : forall t x y, In (existT _ t (x, y)) G -> fst x = y)
        (m : @SymbolicExprContext (interp_flat_type_gen _))
        (HGm : forall t s v,
            lookupb m s = Some v
            -> forall k,
              List.In k (flatten_binding_list (@symbolicify_smart_var interp_base_type t v s) v)
              -> List.In k G)
        (HG2 : forall t x y, In (existT _ t (x, y)) G -> denote_symbolic_expr m (Tbase _) (snd x) = Some y)
        (Hm : forall t sv v,
            lookupb m sv = Some v
            -> denote_symbolic_expr m t sv = Some v)
        (Hwf : wff G e e')
        (Heq : @symbolize_exprf interp_base_type t e = Some s)
    : denote_symbolic_expr m t s = Some (interpf interp_op e').
  Proof.
    cbv beta in *.
    revert dependent m; revert dependent s;
      induction Hwf; simpl; cbv [LetIn.Let_In symbolize_var]; intros; eauto;
        rewrite_hyp ?* by eauto; try reflexivity; eauto;
          cbn [symbolize_exprf option_map] in *;
          repeat first [ reflexivity
                       | progress subst
                       | progress inversion_option
                       | progress cbn [symbolize_exprf] in *
                       | progress unfold option_map in *
                       | break_innermost_match_hyps_step
                       | rewrite denote_symbolize_op in *
                       | progress cbn [denote_symbolic_expr] in *
                       | break_innermost_match_step
                       | progress specialize_by_assumption
                       | solve [ eauto ]
                       | match goal with
                         | [ H : ?v = Some ?x |- Some (interp_op ?s ?d ?opc ?x) = Some (interp_op ?s ?d ?opc ?y) ]
                           => is_var x; cut (v = Some y); [ congruence | clear x H ]
                         | [ H1 : ?v1 = Some ?x1, H2 : ?v2 = Some ?x2 |- Some (?x1, ?x2) = Some (?k1, ?k2) ]
                           => is_var x1; is_var x2; cut (v1 = Some k1 /\ v2 = Some k2);
                              [ clear -H1 H2; intros [? ?]; congruence | clear x1 x2 H1 H2; split ]
                         | [ H : forall x, Some x = Some _ -> _ |- _ ] => specialize (H _ eq_refl)
                         | [ H : forall x, Some _ = Some x -> _ |- _ ] => specialize (H _ eq_refl)
                         | [ IHHwf : _, H : denote_symbolic_expr _ _ _ = None |- _ ]
                           => rewrite IHHwf in H by eauto; discriminate
                         end ].
  Qed.

  Lemma denote_symbolic_expr_norm_symbolize_exprf {t G e e' s}
        (Heq : @norm_symbolize_exprf interp_base_type t e = Some s)
        (m : @SymbolicExprContext (interp_flat_type_gen _))
        (HG : forall t x y, In (existT _ t (x, y)) G -> fst x = y)
        (HGm : forall t s v,
            lookupb m s = Some v
            -> forall k,
              List.In k (flatten_binding_list (@symbolicify_smart_var interp_base_type t v s) v)
              -> List.In k G)
        (HG2 : forall t x y, In (existT _ t (x, y)) G -> denote_symbolic_expr m (Tbase _) (snd x) = Some y)
        (Hm : forall t sv v,
            lookupb m sv = Some v
            -> denote_symbolic_expr m t sv = Some v)
        (Hwf : wff G e e')
    : denote_symbolic_expr m t s = Some (interpf interp_op e').
  Proof.
    unfold norm_symbolize_exprf, option_map in Heq.
    destruct (symbolize_exprf e) eqn:Heq'; inversion_option; subst.
    rewrite denote_symbolic_expr_normalize.
    eapply denote_symbolic_expr_symbolize_exprf; eauto.
  Qed.

  Local Notation context_equiv := (@context_equiv _ _ _ (@SymbolicExprContext interp_flat_type)).
  Require Import Coq.Classes.Morphisms.
  Axiom denote_symbolic_expr_Proper : Proper (context_equiv ==> forall_relation (fun t => eq ==> eq)) denote_symbolic_expr.
  Axiom denote_symbolic_expr_weaken
    : forall c1 c2,
      (forall t n v, lookupb t c1 n = Some v -> lookupb t c2 n = Some v)
      -> forall t sv v,
        denote_symbolic_expr c1 t sv = Some v
        -> denote_symbolic_expr c2 t sv = Some v.
  Axiom denote_symbolic_expr_two_types
    : forall m t0 t1 s,
      denote_symbolic_expr m t0 s <> None
      -> denote_symbolic_expr m t1 s <> None
      -> t0 = t1.

  Local Arguments lookupb : simpl never.
  Local Arguments extendb : simpl never.
  Lemma interpf_csef G t e1 e2
        (m : @SymbolicExprContext (interp_flat_type_gen _))
        (Hwf : wff G e1 e2)
        (HG : forall t x y, In (existT _ t (x, y)) G -> fst x = y)
        (HG2 : forall t x y, In (existT _ t (x, y)) G -> denote_symbolic_expr m (Tbase _) (snd x) = Some y)
        (HGm : forall t s v,
            lookupb m s = Some v
            -> forall k,
                List.In k (flatten_binding_list (@symbolicify_smart_var interp_base_type t v s) v)
                -> List.In k G)
        (Hm : forall t sv v,
            lookupb m sv = Some v
            -> denote_symbolic_expr m t sv = Some v)
    : interpf interp_op (@csef interp_base_type t e1 m) = interpf interp_op e2.
  Proof.
    cbv beta in *.
      revert dependent m;
        induction Hwf; simpl; cbv [LetIn.Let_In symbolize_var]; intros; eauto;
          rewrite_hyp ?* by eauto; try reflexivity; eauto.
      { break_innermost_match_step; [ | admit ].
        break_innermost_match_step; [ | admit ].
        lazymatch goal with
        | [ H : norm_symbolize_exprf _ = Some _ |- _ ]
          => let H' := fresh in
             refine (let H' := denote_symbolic_expr_norm_symbolize_exprf H _ in _); clearbody H';
               specialize_by eauto;
               move H' at top
        end.
        break_innermost_match_step;
          cbn [interpf interpf_step LetIn.Let_In];
          try erewrite_hyp * by eauto.
        all:match goal with
            | [ H : _ |- _ ] => apply H
            end.
        all:repeat setoid_rewrite length_extendb.
        all:try solve [ repeat first [ progress subst
                                     | progress inversion_option
                                     | progress intros *
                                     | progress cbn [eq_rect eq_rec eq_ind]
                                     | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                                     | progress destruct_head'_or
                                     | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                                     | setoid_rewrite in_app_iff
                                     | break_innermost_match_step
                                     | progress simpl in *
                                     | discriminate
                                     | assumption
                                     | symmetry; assumption
                                     | reflexivity
                                     | progress intros
                                     | match goal with
                                       | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                                         => assert (a = b) by (clear -H H'; congruence);
                                            (subst a || subst b)
                                       | [ H : ?x <> ?x |- _ ] => exfalso; apply H; clear
                                       | [ H : lookupb ?t ?m ?n = Some _ |- None = @lookupb _ _ _ ?C ?t' ?m ?n ]
                                         => let H' := fresh in
                                            let RHS := match goal with |- _ = ?RHS => RHS end in
                                            destruct RHS eqn:H'; [ | reflexivity ]
                                       | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None, H : lookupb ?m (SVar ?k') = Some _ |- _ ]
                                         => rewrite Hm_small in H by omega
                                       | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None |- context[lookupb ?m (SVar ?k')] ]
                                         => rewrite Hm_small by omega
                                       | [ H : lookupb ?t ?m ?n = Some _, H' : lookupb ?t' ?m ?n = Some _ |- _ ]
                                         => let H'' := fresh in
                                            pose proof (@lookupb_unique_type _ _ _ _ SymbolicExprContextOk m n t t') as H'';
                                            rewrite H, H' in H'';
                                            specialize_by congruence;
                                            (subst t || subst t')
                                       | [ H : lookupb ?m ?s = Some ?k, H' : denote_symbolic_expr ?m _ ?s = Some ?k', Hm : forall t sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m t sv = Some v |- _ ]
                                         => let H'' := fresh in
                                            pose proof (Hm _ _ _ H) as H'';
                                            rewrite H' in H''; inversion_option;
                                            (subst k || subst k')
                                       | [ H : lookupb ?t ?m ?s = Some ?k, H' : denote_symbolic_expr ?m ?t' ?s = Some ?k', Hm : forall T sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m T sv = Some v |- _ ]
                                         => let H'' := fresh in
                                            let H''' := fresh in
                                            pose proof (Hm _ _ _ H) as H'';
                                            pose proof (denote_symbolic_expr_two_types m t t' s) as H''';
                                            rewrite H', H'' in H''';
                                            specialize_by congruence;
                                            (subst t || subst t')
                                       | [ |- denote_symbolic_expr ?m ?t ?e = Some ?v ]
                                         => lazymatch m with
                                            | extendb ?m' _ _
                                              => apply (fun pf1 => denote_symbolic_expr_weaken m' m pf1 t e v); [ intros ??? | ]
                                            end
                                       end ] ]. }
      Grab Existential Variables.
      { cbn [interpf interpf_step LetIn.Let_In];
          try erewrite_hyp * by eauto.
        clear Heqo.
        all:match goal with
            | [ H : _ |- _ ] => apply H
            end.
        all:try solve [ repeat first [ progress subst
                                     | progress inversion_option
                                     | progress intros *
                                     | progress cbn [eq_rect eq_rec eq_ind]
                                     | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                                     | progress destruct_head'_or
                                     | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                                     | setoid_rewrite in_app_iff
                                     | break_innermost_match_step
                                     | progress simpl in *
                                     | discriminate
                                     | assumption
                                     | symmetry; assumption
                                     | reflexivity
                                     | progress intros
                                     | match goal with
                                       | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                                         => assert (a = b) by (clear -H H'; congruence);
                                            (subst a || subst b)
                                       | [ H : ?x <> ?x |- _ ] => exfalso; apply H; clear
                                       | [ H : lookupb ?t ?m ?n = Some _ |- None = @lookupb _ _ _ ?C ?t' ?m ?n ]
                                         => let H' := fresh in
                                            let RHS := match goal with |- _ = ?RHS => RHS end in
                                            destruct RHS eqn:H'; [ | reflexivity ]
                                       | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None, H : lookupb ?m (SVar ?k') = Some _ |- _ ]
                                         => rewrite Hm_small in H by omega
                                       | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None |- context[lookupb ?m (SVar ?k')] ]
                                         => rewrite Hm_small by omega
                                       | [ H : lookupb ?t ?m ?n = Some _, H' : lookupb ?t' ?m ?n = Some _ |- _ ]
                                         => let H'' := fresh in
                                            pose proof (@lookupb_unique_type _ _ _ _ SymbolicExprContextOk m n t t') as H'';
                                            rewrite H, H' in H'';
                                            specialize_by congruence;
                                            (subst t || subst t')
                                       | [ H : lookupb ?m ?s = Some ?k, H' : denote_symbolic_expr ?m _ ?s = Some ?k', Hm : forall t sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m t sv = Some v |- _ ]
                                         => let H'' := fresh in
                                            pose proof (Hm _ _ _ H) as H'';
                                            rewrite H' in H''; inversion_option;
                                            (subst k || subst k')
                                       | [ H : lookupb ?t ?m ?s = Some ?k, H' : denote_symbolic_expr ?m ?t' ?s = Some ?k', Hm : forall T sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m T sv = Some v |- _ ]
                                         => let H'' := fresh in
                                            let H''' := fresh in
                                            pose proof (Hm _ _ _ H) as H'';
                                            pose proof (denote_symbolic_expr_two_types m t t' s) as H''';
                                            rewrite H', H'' in H''';
                                            specialize_by congruence;
                                            (subst t || subst t')
                                       | [ |- denote_symbolic_expr ?m ?t ?e = Some ?v ]
                                         => lazymatch m with
                                            | extendb ?m' _ _
                                              => apply (fun pf1 => denote_symbolic_expr_weaken m' m pf1 t e v); [ intros ??? | ]
                                            end
                                       end ] ].
        all:try (setoid_rewrite in_app_iff; intros; destruct_head'_or).
        all:intros;match goal with
        | [ |- denote_symbolic_expr ?m ?t ?e = Some ?v ]
          => lazymatch m with
             | extendb ?m' _ _
               => apply (fun pf1 => denote_symbolic_expr_weaken m' m pf1 t e v); [ intros ??? | ]
             end
        end.
        all:try solve [ repeat first [ progress subst
                                     | progress inversion_option
                                     | progress intros *
                                     | progress cbn [eq_rect eq_rec eq_ind]
                                     | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                                     | progress destruct_head'_or
                                     | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                                     | setoid_rewrite in_app_iff
                                     | break_innermost_match_step
                                     | progress simpl in *
                                     | discriminate
                                     | assumption
                                     | symmetry; assumption
                                     | reflexivity
                                     | progress intros
                                     | match goal with
                                       | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                                         => assert (a = b) by (clear -H H'; congruence);
                                            (subst a || subst b)
                                       | [ H : ?x <> ?x |- _ ] => exfalso; apply H; clear
                                       | [ H : lookupb ?t ?m ?n = Some _ |- None = @lookupb _ _ _ ?C ?t' ?m ?n ]
                                         => let H' := fresh in
                                            let RHS := match goal with |- _ = ?RHS => RHS end in
                                            destruct RHS eqn:H'; [ | reflexivity ]
                                       | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None, H : lookupb ?m (SVar ?k') = Some _ |- _ ]
                                         => rewrite Hm_small in H by omega
                                       | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None |- context[lookupb ?m (SVar ?k')] ]
                                         => rewrite Hm_small by omega
                                       | [ H : lookupb ?t ?m ?n = Some _, H' : lookupb ?t' ?m ?n = Some _ |- _ ]
                                         => let H'' := fresh in
                                            pose proof (@lookupb_unique_type _ _ _ _ SymbolicExprContextOk m n t t') as H'';
                                            rewrite H, H' in H'';
                                            specialize_by congruence;
                                            (subst t || subst t')
                                       | [ H : lookupb ?m ?s = Some ?k, H' : denote_symbolic_expr ?m _ ?s = Some ?k', Hm : forall t sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m t sv = Some v |- _ ]
                                         => let H'' := fresh in
                                            pose proof (Hm _ _ _ H) as H'';
                                            rewrite H' in H''; inversion_option;
                                            (subst k || subst k')
                                       | [ H : lookupb ?t ?m ?s = Some ?k, H' : denote_symbolic_expr ?m ?t' ?s = Some ?k', Hm : forall T sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m T sv = Some v |- _ ]
                                         => let H'' := fresh in
                                            let H''' := fresh in
                                            pose proof (Hm _ _ _ H) as H'';
                                            pose proof (denote_symbolic_expr_two_types m t t' s) as H''';
                                            rewrite H', H'' in H''';
                                            specialize_by congruence;
                                            (subst t || subst t')
                                       | [ |- denote_symbolic_expr ?m ?t ?e = Some ?v ]
                                         => lazymatch m with
                                            | extendb ?m' _ _
                                              => apply (fun pf1 => denote_symbolic_expr_weaken m' m pf1 t e v); [ intros ??? | ]
                                            end
                                       end ] ].
        Focus 2.
        { match goal with
          | [ |- denote_symbolic_expr ?m ?t ?e = Some ?v ]
            => lazymatch m with
               | extendb ?m' _ _
                 => apply (fun pf1 => denote_symbolic_expr_weaken m' m pf1 t e v); [ intros ??? | ]
               end
          end.
        all:try solve [ repeat first [ progress subst
                                     | progress inversion_option
                                     | progress intros *
                                     | progress cbn [eq_rect eq_rec eq_ind]
                                     | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                                     | progress destruct_head'_or
                                     | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                                     | setoid_rewrite in_app_iff
                                     | break_innermost_match_step
                                     | progress simpl in *
                                     | discriminate
                                     | assumption
                                     | symmetry; assumption
                                     | reflexivity
                                     | progress intros
                                     | match goal with
                                       | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                                         => assert (a = b) by (clear -H H'; congruence);
                                            (subst a || subst b)
                                       | [ H : ?x <> ?x |- _ ] => exfalso; apply H; clear
                                       | [ H : lookupb ?t ?m ?n = Some _ |- None = @lookupb _ _ _ ?C ?t' ?m ?n ]
                                         => let H' := fresh in
                                            let RHS := match goal with |- _ = ?RHS => RHS end in
                                            destruct RHS eqn:H'; [ | reflexivity ]
                                       | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None, H : lookupb ?m (SVar ?k') = Some _ |- _ ]
                                         => rewrite Hm_small in H by omega
                                       | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None |- context[lookupb ?m (SVar ?k')] ]
                                         => rewrite Hm_small by omega
                                       | [ H : lookupb ?t ?m ?n = Some _, H' : lookupb ?t' ?m ?n = Some _ |- _ ]
                                         => let H'' := fresh in
                                            pose proof (@lookupb_unique_type _ _ _ _ SymbolicExprContextOk m n t t') as H'';
                                            rewrite H, H' in H'';
                                            specialize_by congruence;
                                            (subst t || subst t')
                                       | [ H : lookupb ?m ?s = Some ?k, H' : denote_symbolic_expr ?m _ ?s = Some ?k', Hm : forall t sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m t sv = Some v |- _ ]
                                         => let H'' := fresh in
                                            pose proof (Hm _ _ _ H) as H'';
                                            rewrite H' in H''; inversion_option;
                                            (subst k || subst k')
                                       | [ H : lookupb ?t ?m ?s = Some ?k, H' : denote_symbolic_expr ?m ?t' ?s = Some ?k', Hm : forall T sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m T sv = Some v |- _ ]
                                         => let H'' := fresh in
                                            let H''' := fresh in
                                            pose proof (Hm _ _ _ H) as H'';
                                            pose proof (denote_symbolic_expr_two_types m t t' s) as H''';
                                            rewrite H', H'' in H''';
                                            specialize_by congruence;
                                            (subst t || subst t')
                                       | [ |- denote_symbolic_expr ?m ?t ?e = Some ?v ]
                                         => lazymatch m with
                                            | extendb ?m' _ _
                                              => apply (fun pf1 => denote_symbolic_expr_weaken m' m pf1 t e v); [ intros ??? | ]
                                            end
                                       end ] ].

        repeat first [ progress subst
                                     | progress inversion_option
                                     | progress intros *
                                     | progress cbn [eq_rect eq_rec eq_ind]
                                     | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                                     | progress destruct_head'_or
                                     | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                                     | setoid_rewrite in_app_iff
                                     | break_innermost_match_step
                                     | progress simpl in *
                                     | discriminate
                                     | assumption
                                     | symmetry; assumption
                                     | reflexivity
                                     | progress intros
                                     | match goal with
                                       | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                                         => assert (a = b) by (clear -H H'; congruence);
                                            (subst a || subst b)
                                       | [ H : ?x <> ?x |- _ ] => exfalso; apply H; clear
                                       | [ H : lookupb ?t ?m ?n = Some _ |- None = @lookupb _ _ _ ?C ?t' ?m ?n ]
                                         => let H' := fresh in
                                            let RHS := match goal with |- _ = ?RHS => RHS end in
                                            destruct RHS eqn:H'; [ | reflexivity ]
                                       | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None, H : lookupb ?m (SVar ?k') = Some _ |- _ ]
                                         => rewrite Hm_small in H by omega
                                       | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None |- context[lookupb ?m (SVar ?k')] ]
                                         => rewrite Hm_small by omega
                                       | [ H : lookupb ?t ?m ?n = Some _, H' : lookupb ?t' ?m ?n = Some _ |- _ ]
                                         => let H'' := fresh in
                                            pose proof (@lookupb_unique_type _ _ _ _ SymbolicExprContextOk m n t t') as H'';
                                            rewrite H, H' in H'';
                                            specialize_by congruence;
                                            (subst t || subst t')
                                       | [ H : lookupb ?m ?s = Some ?k, H' : denote_symbolic_expr ?m _ ?s = Some ?k', Hm : forall t sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m t sv = Some v |- _ ]
                                         => let H'' := fresh in
                                            pose proof (Hm _ _ _ H) as H'';
                                            rewrite H' in H''; inversion_option;
                                            (subst k || subst k')
                                       | [ H : lookupb ?t ?m ?s = Some ?k, H' : denote_symbolic_expr ?m ?t' ?s = Some ?k', Hm : forall T sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m T sv = Some v |- _ ]
                                         => let H'' := fresh in
                                            let H''' := fresh in
                                            pose proof (Hm _ _ _ H) as H'';
                                            pose proof (denote_symbolic_expr_two_types m t t' s) as H''';
                                            rewrite H', H'' in H''';
                                            specialize_by congruence;
                                            (subst t || subst t')
                                       | [ |- denote_symbolic_expr ?m ?t ?e = Some ?v ]
                                         => lazymatch m with
                                            | extendb ?m' _ _
                                              => apply (fun pf1 => denote_symbolic_expr_weaken m' m pf1 t e v); [ intros ??? | ]
                                            end
                                       end ].
        Focus 2.
        all:try solve [ repeat first [ progress subst
                                     | progress inversion_option
                                     | progress intros *
                                     | progress cbn [eq_rect eq_rec eq_ind]
                                     | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                                     | progress destruct_head'_or
                                     | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                                     | setoid_rewrite in_app_iff
                                     | break_innermost_match_step
                                     | progress simpl in *
                                     | discriminate
                                     | assumption
                                     | symmetry; assumption
                                     | reflexivity
                                     | progress intros
                                     | match goal with
                                       | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                                         => assert (a = b) by (clear -H H'; congruence);
                                            (subst a || subst b)
                                       | [ H : ?x <> ?x |- _ ] => exfalso; apply H; clear
                                       | [ H : lookupb ?t ?m ?n = Some _ |- None = @lookupb _ _ _ ?C ?t' ?m ?n ]
                                         => let H' := fresh in
                                            let RHS := match goal with |- _ = ?RHS => RHS end in
                                            destruct RHS eqn:H'; [ | reflexivity ]
                                       | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None, H : lookupb ?m (SVar ?k') = Some _ |- _ ]
                                         => rewrite Hm_small in H by omega
                                       | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None |- context[lookupb ?m (SVar ?k')] ]
                                         => rewrite Hm_small by omega
                                       | [ H : lookupb ?t ?m ?n = Some _, H' : lookupb ?t' ?m ?n = Some _ |- _ ]
                                         => let H'' := fresh in
                                            pose proof (@lookupb_unique_type _ _ _ _ SymbolicExprContextOk m n t t') as H'';
                                            rewrite H, H' in H'';
                                            specialize_by congruence;
                                            (subst t || subst t')
                                       | [ H : lookupb ?m ?s = Some ?k, H' : denote_symbolic_expr ?m _ ?s = Some ?k', Hm : forall t sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m t sv = Some v |- _ ]
                                         => let H'' := fresh in
                                            pose proof (Hm _ _ _ H) as H'';
                                            rewrite H' in H''; inversion_option;
                                            (subst k || subst k')
                                       | [ H : lookupb ?t ?m ?s = Some ?k, H' : denote_symbolic_expr ?m ?t' ?s = Some ?k', Hm : forall T sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m T sv = Some v |- _ ]
                                         => let H'' := fresh in
                                            let H''' := fresh in
                                            pose proof (Hm _ _ _ H) as H'';
                                            pose proof (denote_symbolic_expr_two_types m t t' s) as H''';
                                            rewrite H', H'' in H''';
                                            specialize_by congruence;
                                            (subst t || subst t')
                                       | [ |- denote_symbolic_expr ?m ?t ?e = Some ?v ]
                                         => lazymatch m with
                                            | extendb ?m' _ _
                                              => apply (fun pf1 => denote_symbolic_expr_weaken m' m pf1 t e v); [ intros ??? | ]
                                            end
                                       end ]

                        | repeat first [ progress cbn [denote_symbolic_expr fst snd projT1 projT2]
                                       | setoid_rewrite length_extendb
                                       | rewrite Nat.sub_diag
                                       | reflexivity
                                       | discriminate
                                       | rewrite eq_trans_sym_inv_r
                                       | progress simpl @nth_error
                                       | progress unfold var_cast;
                                         break_innermost_match
                                       | match goal with
                                         | [ H : context[flat_type_beq _ _ ?x ?x] |- _ ]
                                           => setoid_rewrite (flat_type_dec_lb _ _ base_type_code_lb x x eq_refl) in H
                                         end ] ].
        {

          repeat first [ progress subst
                                     | progress inversion_option
                                     | progress intros *
                                     | progress cbn [eq_rect eq_rec eq_ind]
                                     | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                                     | progress destruct_head'_or
                                     | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                                     | setoid_rewrite in_app_iff
                                     | break_innermost_match_step
                                     | progress simpl in *
                                     | discriminate
                                     | assumption
                                     | symmetry; assumption
                                     | reflexivity
                                     | progress intros
                                     | match goal with
                                       | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                                         => assert (a = b) by (clear -H H'; congruence);
                                            (subst a || subst b)
                                       | [ H : ?x <> ?x |- _ ] => exfalso; apply H; clear
                                       | [ H : lookupb ?t ?m ?n = Some _ |- None = @lookupb _ _ _ ?C ?t' ?m ?n ]
                                         => let H' := fresh in
                                            let RHS := match goal with |- _ = ?RHS => RHS end in
                                            destruct RHS eqn:H'; [ | reflexivity ]
                                       | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None, H : lookupb ?m (SVar ?k') = Some _ |- _ ]
                                         => rewrite Hm_small in H by omega
                                       | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None |- context[lookupb ?m (SVar ?k')] ]
                                         => rewrite Hm_small by omega
                                       | [ H : lookupb ?t ?m ?n = Some _, H' : lookupb ?t' ?m ?n = Some _ |- _ ]
                                         => let H'' := fresh in
                                            pose proof (@lookupb_unique_type _ _ _ _ SymbolicExprContextOk m n t t') as H'';
                                            rewrite H, H' in H'';
                                            specialize_by congruence;
                                            (subst t || subst t')
                                       | [ H : lookupb ?m ?s = Some ?k, H' : denote_symbolic_expr ?m _ ?s = Some ?k', Hm : forall t sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m t sv = Some v |- _ ]
                                         => let H'' := fresh in
                                            pose proof (Hm _ _ _ H) as H'';
                                            rewrite H' in H''; inversion_option;
                                            (subst k || subst k')
                                       | [ H : lookupb ?t ?m ?s = Some ?k, H' : denote_symbolic_expr ?m ?t' ?s = Some ?k', Hm : forall T sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m T sv = Some v |- _ ]
                                         => let H'' := fresh in
                                            let H''' := fresh in
                                            pose proof (Hm _ _ _ H) as H'';
                                            pose proof (denote_symbolic_expr_two_types m t t' s) as H''';
                                            rewrite H', H'' in H''';
                                            specialize_by congruence;
                                            (subst t || subst t')
                                       end ].
        all:try solve [ repeat first [ progress subst
                                     | progress inversion_option
                                     | progress intros *
                                     | progress cbn [eq_rect eq_rec eq_ind]
                                     | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                                     | progress destruct_head'_or
                                     | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                                     | setoid_rewrite in_app_iff
                                     | break_innermost_match_step
                                     | progress simpl in *
                                     | discriminate
                                     | assumption
                                     | symmetry; assumption
                                     | reflexivity
                                     | progress intros
                                     | match goal with
                                       | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                                         => assert (a = b) by (clear -H H'; congruence);
                                            (subst a || subst b)
                                       | [ H : ?x <> ?x |- _ ] => exfalso; apply H; clear
                                       | [ H : lookupb ?t ?m ?n = Some _ |- None = @lookupb _ _ _ ?C ?t' ?m ?n ]
                                         => let H' := fresh in
                                            let RHS := match goal with |- _ = ?RHS => RHS end in
                                            destruct RHS eqn:H'; [ | reflexivity ]
                                       | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None, H : lookupb ?m (SVar ?k') = Some _ |- _ ]
                                         => rewrite Hm_small in H by omega
                                       | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None |- context[lookupb ?m (SVar ?k')] ]
                                         => rewrite Hm_small by omega
                                       | [ H : lookupb ?t ?m ?n = Some _, H' : lookupb ?t' ?m ?n = Some _ |- _ ]
                                         => let H'' := fresh in
                                            pose proof (@lookupb_unique_type _ _ _ _ SymbolicExprContextOk m n t t') as H'';
                                            rewrite H, H' in H'';
                                            specialize_by congruence;
                                            (subst t || subst t')
                                       | [ H : lookupb ?m ?s = Some ?k, H' : denote_symbolic_expr ?m _ ?s = Some ?k', Hm : forall t sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m t sv = Some v |- _ ]
                                         => let H'' := fresh in
                                            pose proof (Hm _ _ _ H) as H'';
                                            rewrite H' in H''; inversion_option;
                                            (subst k || subst k')
                                       | [ H : lookupb ?t ?m ?s = Some ?k, H' : denote_symbolic_expr ?m ?t' ?s = Some ?k', Hm : forall T sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m T sv = Some v |- _ ]
                                         => let H'' := fresh in
                                            let H''' := fresh in
                                            pose proof (Hm _ _ _ H) as H'';
                                            pose proof (denote_symbolic_expr_two_types m t t' s) as H''';
                                            rewrite H', H'' in H''';
                                            specialize_by congruence;
                                            (subst t || subst t')
                                       | [ |- denote_symbolic_expr ?m ?t ?e = Some ?v ]
                                         => lazymatch m with
                                            | extendb ?m' _ _
                                              => apply (fun pf1 => denote_symbolic_expr_weaken m' m pf1 t e v); [ intros ??? | ]
                                            end
                                       end ]

                        | repeat first [ progress cbn [denote_symbolic_expr fst snd projT1 projT2]
                                       | setoid_rewrite length_extendb
                                       | rewrite Nat.sub_diag
                                       | reflexivity
                                       | discriminate
                                       | rewrite eq_trans_sym_inv_r
                                       | progress simpl @nth_error
                                       | progress unfold var_cast;
                                         break_innermost_match
                                       | match goal with
                                         | [ H : context[flat_type_beq _ _ ?x ?x] |- _ ]
                                           => setoid_rewrite (flat_type_dec_lb _ _ base_type_code_lb x x eq_refl) in H
                                         end ] ].

                                       | [ |- denote_symbolic_expr ?m ?t ?e = Some ?v ]
                                         => lazymatch m with
                                            | extendb ?m' _ _
                                              => apply (fun pf1 => denote_symbolic_expr_weaken m' m pf1 t e v); [ intros ??? | ]
                                            end
                                       end ]
                      .
        2:try solve [ repeat first [ progress subst
                                     | progress inversion_option
                                     | progress intros *
                                     | progress cbn [eq_rect eq_rec eq_ind]
                                     | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                                     | progress destruct_head'_or
                                     | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                                     | setoid_rewrite in_app_iff
                                     | break_innermost_match_step
                                     | progress simpl in *
                                     | discriminate
                                     | assumption
                                     | symmetry; assumption
                                     | reflexivity
                                     | progress intros
                                     | match goal with
                                       | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                                         => assert (a = b) by (clear -H H'; congruence);
                                            (subst a || subst b)
                                       | [ H : ?x <> ?x |- _ ] => exfalso; apply H; clear
                                       | [ H : lookupb ?t ?m ?n = Some _ |- None = @lookupb _ _ _ ?C ?t' ?m ?n ]
                                         => let H' := fresh in
                                            let RHS := match goal with |- _ = ?RHS => RHS end in
                                            destruct RHS eqn:H'; [ | reflexivity ]
                                       | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None, H : lookupb ?m (SVar ?k') = Some _ |- _ ]
                                         => rewrite Hm_small in H by omega
                                       | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None |- context[lookupb ?m (SVar ?k')] ]
                                         => rewrite Hm_small by omega
                                       | [ H : lookupb ?t ?m ?n = Some _, H' : lookupb ?t' ?m ?n = Some _ |- _ ]
                                         => let H'' := fresh in
                                            pose proof (@lookupb_unique_type _ _ _ _ SymbolicExprContextOk m n t t') as H'';
                                            rewrite H, H' in H'';
                                            specialize_by congruence;
                                            (subst t || subst t')
                                       | [ H : lookupb ?m ?s = Some ?k, H' : denote_symbolic_expr ?m _ ?s = Some ?k', Hm : forall t sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m t sv = Some v |- _ ]
                                         => let H'' := fresh in
                                            pose proof (Hm _ _ _ H) as H'';
                                            rewrite H' in H''; inversion_option;
                                            (subst k || subst k')
                                       | [ H : lookupb ?t ?m ?s = Some ?k, H' : denote_symbolic_expr ?m ?t' ?s = Some ?k', Hm : forall T sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m T sv = Some v |- _ ]
                                         => let H'' := fresh in
                                            let H''' := fresh in
                                            pose proof (Hm _ _ _ H) as H'';
                                            pose proof (denote_symbolic_expr_two_types m t t' s) as H''';
                                            rewrite H', H'' in H''';
                                            specialize_by congruence;
                                            (subst t || subst t')
                                       | [ |- denote_symbolic_expr ?m ?t ?e = Some ?v ]
                                         => lazymatch m with
                                            | extendb ?m' _ _
                                              => apply (fun pf1 => denote_symbolic_expr_weaken m' m pf1 t e v); [ intros ??? | ]
                                            end
                                       end ] ].
        Focus 2.
        { repeat first [ progress subst
                                     | progress inversion_option
                                     | progress intros *
                                     | progress cbn [eq_rect eq_rec eq_ind]
                                     | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                                     | progress destruct_head'_or
                                     | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                                     | setoid_rewrite in_app_iff
                                     | break_innermost_match_step
                                     | progress simpl in *
                                     | discriminate
                                     | assumption
                                     | symmetry; assumption
                                     | reflexivity
                                     | progress intros
                                     | match goal with
                                       | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                                         => assert (a = b) by (clear -H H'; congruence);
                                            (subst a || subst b)
                                       | [ H : ?x <> ?x |- _ ] => exfalso; apply H; clear
                                       | [ H : lookupb ?t ?m ?n = Some _ |- None = @lookupb _ _ _ ?C ?t' ?m ?n ]
                                         => let H' := fresh in
                                            let RHS := match goal with |- _ = ?RHS => RHS end in
                                            destruct RHS eqn:H'; [ | reflexivity ]
                                       | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None, H : lookupb ?m (SVar ?k') = Some _ |- _ ]
                                         => rewrite Hm_small in H by omega
                                       | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None |- context[lookupb ?m (SVar ?k')] ]
                                         => rewrite Hm_small by omega
                                       | [ H : lookupb ?t ?m ?n = Some _, H' : lookupb ?t' ?m ?n = Some _ |- _ ]
                                         => let H'' := fresh in
                                            pose proof (@lookupb_unique_type _ _ _ _ SymbolicExprContextOk m n t t') as H'';
                                            rewrite H, H' in H'';
                                            specialize_by congruence;
                                            (subst t || subst t')
                                       | [ H : lookupb ?m ?s = Some ?k, H' : denote_symbolic_expr ?m _ ?s = Some ?k', Hm : forall t sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m t sv = Some v |- _ ]
                                         => let H'' := fresh in
                                            pose proof (Hm _ _ _ H) as H'';
                                            rewrite H' in H''; inversion_option;
                                            (subst k || subst k')
                                       | [ H : lookupb ?t ?m ?s = Some ?k, H' : denote_symbolic_expr ?m ?t' ?s = Some ?k', Hm : forall T sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m T sv = Some v |- _ ]
                                         => let H'' := fresh in
                                            let H''' := fresh in
                                            pose proof (Hm _ _ _ H) as H'';
                                            pose proof (denote_symbolic_expr_two_types m t t' s) as H''';
                                            rewrite H', H'' in H''';
                                            specialize_by congruence;
                                            (subst t || subst t')
                                       | [ |- denote_symbolic_expr ?m ?t ?e = Some ?v ]
                                         => lazymatch m with
                                            | extendb ?m' _ _
                                              => apply (fun pf1 => denote_symbolic_expr_weaken m' m pf1 t e v); [ intros ??? | ]
                                            end
                                       end ].


        { repeat first [ progress subst
                                     | progress inversion_option
                                     | progress intros *
                                     | progress cbn [eq_rect eq_rec eq_ind]
                                     | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                                     | progress destruct_head'_or
                                     | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                                     | setoid_rewrite in_app_iff
                                     | break_innermost_match_step
                                     | progress simpl in *
                                     | discriminate
                                     | assumption
                                     | symmetry; assumption
                                     | reflexivity
                                     | progress intros
                                     | match goal with
                                       | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                                         => assert (a = b) by (clear -H H'; congruence);
                                            (subst a || subst b)
                                       | [ H : ?x <> ?x |- _ ] => exfalso; apply H; clear
                                       | [ H : lookupb ?t ?m ?n = Some _ |- None = @lookupb _ _ _ ?C ?t' ?m ?n ]
                                         => let H' := fresh in
                                            let RHS := match goal with |- _ = ?RHS => RHS end in
                                            destruct RHS eqn:H'; [ | reflexivity ]
                                       | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None, H : lookupb ?m (SVar ?k') = Some _ |- _ ]
                                         => rewrite Hm_small in H by omega
                                       | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None |- context[lookupb ?m (SVar ?k')] ]
                                         => rewrite Hm_small by omega
                                       | [ H : lookupb ?t ?m ?n = Some _, H' : lookupb ?t' ?m ?n = Some _ |- _ ]
                                         => let H'' := fresh in
                                            pose proof (@lookupb_unique_type _ _ _ _ SymbolicExprContextOk m n t t') as H'';
                                            rewrite H, H' in H'';
                                            specialize_by congruence;
                                            (subst t || subst t')
                                       | [ H : lookupb ?m ?s = Some ?k, H' : denote_symbolic_expr ?m _ ?s = Some ?k', Hm : forall t sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m t sv = Some v |- _ ]
                                         => let H'' := fresh in
                                            pose proof (Hm _ _ _ H) as H'';
                                            rewrite H' in H''; inversion_option;
                                            (subst k || subst k')
                                       | [ H : lookupb ?t ?m ?s = Some ?k, H' : denote_symbolic_expr ?m ?t' ?s = Some ?k', Hm : forall T sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m T sv = Some v |- _ ]
                                         => let H'' := fresh in
                                            let H''' := fresh in
                                            pose proof (Hm _ _ _ H) as H'';
                                            pose proof (denote_symbolic_expr_two_types m t t' s) as H''';
                                            rewrite H', H'' in H''';
                                            specialize_by congruence;
                                            (subst t || subst t')
                                       end ].
          admit. }
        { repeat first [ progress subst
                       | progress inversion_option
                       | progress intros *
                       | progress cbn [eq_rect eq_rec eq_ind]
                       | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                       | progress destruct_head'_or
                       | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                       | setoid_rewrite in_app_iff
                       | break_innermost_match_step
                       | progress simpl in *
                       | discriminate
                       | assumption
                       | symmetry; assumption
                       | reflexivity
                       | progress intros
                       | match goal with
                         | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                           => assert (a = b) by (clear -H H'; congruence);
                              (subst a || subst b)
                         | [ H : ?x <> ?x |- _ ] => exfalso; apply H; clear
                         | [ H : lookupb ?t ?m ?n = Some _ |- None = @lookupb _ _ _ ?C ?t' ?m ?n ]
                           => let H' := fresh in
                              let RHS := match goal with |- _ = ?RHS => RHS end in
                              destruct RHS eqn:H'; [ | reflexivity ]
                         | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None, H : lookupb ?m (SVar ?k') = Some _ |- _ ]
                           => rewrite Hm_small in H by omega
                         | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None |- context[lookupb ?m (SVar ?k')] ]
                           => rewrite Hm_small by omega
                         | [ H : lookupb ?t ?m ?n = Some _, H' : lookupb ?t' ?m ?n = Some _ |- _ ]
                           => let H'' := fresh in
                              pose proof (@lookupb_unique_type _ _ _ _ SymbolicExprContextOk m n t t') as H'';
                              rewrite H, H' in H'';
                              specialize_by congruence;
                              (subst t || subst t')
                         | [ H : lookupb ?m ?s = Some ?k, H' : denote_symbolic_expr ?m _ ?s = Some ?k', Hm : forall t sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m t sv = Some v |- _ ]
                           => let H'' := fresh in
                              pose proof (Hm _ _ _ H) as H'';
                              rewrite H' in H''; inversion_option;
                              (subst k || subst k')
                         | [ H : lookupb ?t ?m ?s = Some ?k, H' : denote_symbolic_expr ?m ?t' ?s = Some ?k', Hm : forall T sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m T sv = Some v |- _ ]
                           => let H'' := fresh in
                              let H''' := fresh in
                              pose proof (Hm _ _ _ H) as H'';
                              pose proof (denote_symbolic_expr_two_types m t t' s) as H''';
                              rewrite H', H'' in H''';
                              specialize_by congruence;
                              (subst t || subst t')
                         end ].
          { eapply denote_symbolic_expr_flatten_binding_list.
            all:repeat first [ progress subst
                           | progress inversion_option
                           | progress intros *
                           | progress cbn [eq_rect eq_rec eq_ind]
                           | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                           | progress destruct_head'_or
                           | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                           | setoid_rewrite in_app_iff
                           | break_innermost_match_step
                           | intros; progress inversion_option ].
          all:try solve [ repeat first [ progress subst
                                       | progress inversion_option
                                       | progress intros *
                                       | progress cbn [eq_rect eq_rec eq_ind]
                                       | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                                       | progress destruct_head'_or
                                       | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                                       | setoid_rewrite in_app_iff
                                       | break_innermost_match_step
                                       | progress simpl in *
                                       | discriminate
                                       | assumption
                                       | symmetry; assumption
                                       | reflexivity
                                       | progress intros
                                       | match goal with
                                         | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                                           => assert (a = b) by (clear -H H'; congruence);
                                              (subst a || subst b)
                                         | [ H : ?x <> ?x |- _ ] => exfalso; apply H; clear
                                         | [ H : lookupb ?t ?m ?n = Some _ |- None = @lookupb _ _ _ ?C ?t' ?m ?n ]
                                           => let H' := fresh in
                                              let RHS := match goal with |- _ = ?RHS => RHS end in
                                              destruct RHS eqn:H'; [ | reflexivity ]
                                         | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None, H : lookupb ?m (SVar ?k') = Some _ |- _ ]
                                           => rewrite Hm_small in H by omega
                                         | [ H : lookupb ?t ?m ?n = Some _, H' : lookupb ?t' ?m ?n = Some _ |- _ ]
                                           => let H'' := fresh in
                                              pose proof (@lookupb_unique_type _ _ _ _ SymbolicExprContextOk m n t t') as H'';
                                              rewrite H, H' in H'';
                                              specialize_by congruence;
                                              (subst t || subst t')
                                         | [ H : lookupb ?m ?s = Some ?k, H' : denote_symbolic_expr ?m _ ?s = Some ?k', Hm : forall t sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m t sv = Some v |- _ ]
                                           => let H'' := fresh in
                                              pose proof (Hm _ _ _ H) as H'';
                                              rewrite H' in H''; inversion_option;
                                              (subst k || subst k')
                                         | [ H : lookupb ?t ?m ?s = Some ?k, H' : denote_symbolic_expr ?m ?t' ?s = Some ?k', Hm : forall T sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m T sv = Some v |- _ ]
                                           => let H'' := fresh in
                                              let H''' := fresh in
                                              pose proof (Hm _ _ _ H) as H'';
                                              pose proof (denote_symbolic_expr_two_types m t t' s) as H''';
                                              rewrite H', H'' in H''';
                                              specialize_by congruence;
                                              (subst t || subst t')
                                         | [ |- denote_symbolic_expr ?m ?t ?e = Some ?v ]
                                           => lazymatch m with
                                              | extendb ?m' _ _
                                                => apply (fun pf1 => denote_symbolic_expr_weaken m' m pf1 t e v); [ intros ??? | ]
                                              end
                                         end ]
                        | repeat first [ progress cbn [denote_symbolic_expr fst snd projT1 projT2]
                                       | setoid_rewrite length_extendb
                                       | rewrite Nat.sub_diag
                                       | reflexivity
                                       | discriminate
                                       | rewrite eq_trans_sym_inv_r
                                       | progress simpl @nth_error
                                       | progress unfold var_cast;
                                         break_innermost_match
                                       | match goal with
                                         | [ H : context[flat_type_beq _ _ ?x ?x] |- _ ]
                                           => setoid_rewrite (flat_type_dec_lb _ _ base_type_code_lb x x eq_refl) in H
                                         end ] ]. }
          all:try solve [ repeat first [ progress subst
                                       | progress inversion_option
                                       | progress intros *
                                       | progress cbn [eq_rect eq_rec eq_ind]
                                       | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                                       | progress destruct_head'_or
                                       | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                                       | setoid_rewrite in_app_iff
                                       | break_innermost_match_step
                                       | progress simpl in *
                                       | discriminate
                                       | assumption
                                       | symmetry; assumption
                                       | reflexivity
                                       | progress intros
                                       | match goal with
                                         | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                                           => assert (a = b) by (clear -H H'; congruence);
                                              (subst a || subst b)
                                         | [ H : ?x <> ?x |- _ ] => exfalso; apply H; clear
                                         | [ H : lookupb ?t ?m ?n = Some _ |- None = @lookupb _ _ _ ?C ?t' ?m ?n ]
                                           => let H' := fresh in
                                              let RHS := match goal with |- _ = ?RHS => RHS end in
                                              destruct RHS eqn:H'; [ | reflexivity ]
                                         | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None, H : lookupb ?m (SVar ?k') = Some _ |- _ ]
                                           => rewrite Hm_small in H by omega
                                         | [ H : lookupb ?t ?m ?n = Some _, H' : lookupb ?t' ?m ?n = Some _ |- _ ]
                                           => let H'' := fresh in
                                              pose proof (@lookupb_unique_type _ _ _ _ SymbolicExprContextOk m n t t') as H'';
                                              rewrite H, H' in H'';
                                              specialize_by congruence;
                                              (subst t || subst t')
                                         | [ H : lookupb ?m ?s = Some ?k, H' : denote_symbolic_expr ?m _ ?s = Some ?k', Hm : forall t sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m t sv = Some v |- _ ]
                                           => let H'' := fresh in
                                              pose proof (Hm _ _ _ H) as H'';
                                              rewrite H' in H''; inversion_option;
                                              (subst k || subst k')
                                         | [ H : lookupb ?t ?m ?s = Some ?k, H' : denote_symbolic_expr ?m ?t' ?s = Some ?k', Hm : forall T sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m T sv = Some v |- _ ]
                                           => let H'' := fresh in
                                              let H''' := fresh in
                                              pose proof (Hm _ _ _ H) as H'';
                                              pose proof (denote_symbolic_expr_two_types m t t' s) as H''';
                                              rewrite H', H'' in H''';
                                              specialize_by congruence;
                                              (subst t || subst t')
                                         | [ |- denote_symbolic_expr ?m ?t ?e = Some ?v ]
                                           => lazymatch m with
                                              | extendb ?m' _ _
                                                => apply (fun pf1 => denote_symbolic_expr_weaken m' m pf1 t e v); [ intros ??? | ]
                                              end
                                         end ]
                        | repeat first [ progress cbn [denote_symbolic_expr fst snd projT1 projT2]
                                       | setoid_rewrite length_extendb
                                       | rewrite Nat.sub_diag
                                       | reflexivity
                                       | discriminate
                                       | rewrite eq_trans_sym_inv_r
                                       | progress simpl @nth_error
                                       | progress unfold var_cast;
                                         break_innermost_match
                                       | match goal with
                                         | [ H : context[flat_type_beq _ _ ?x ?x] |- _ ]
                                           => setoid_rewrite (flat_type_dec_lb _ _ base_type_code_lb x x eq_refl) in H
                                         end ] ]. }
        all:repeat setoid_rewrite length_extendb.
        all:repeat setoid_rewrite in_app_iff.
        all:intros *.
        all:rewrite ?(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk).
        all:break_innermost_match; subst.
        all:cbn [eq_rect eq_rec eq_ind]; inversion_option.
        all:try (intro; progress inversion_option).
        all:subst.
        all:try solve [ repeat first [ progress subst
                                       | progress inversion_option
                                       | progress intros *
                                       | progress cbn [eq_rect eq_rec eq_ind]
                                       | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                                       | progress destruct_head'_or
                                       | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                                       | setoid_rewrite in_app_iff
                                       | break_innermost_match_step
                                       | progress simpl in *
                                       | discriminate
                                       | assumption
                                       | symmetry; assumption
                                       | reflexivity
                                       | progress intros
                                       | match goal with
                                         | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                                           => assert (a = b) by (clear -H H'; congruence);
                                              (subst a || subst b)
                                         | [ H : ?x <> ?x |- _ ] => exfalso; apply H; clear
                                         | [ H : lookupb ?t ?m ?n = Some _ |- None = @lookupb _ _ _ ?C ?t' ?m ?n ]
                                           => let H' := fresh in
                                              let RHS := match goal with |- _ = ?RHS => RHS end in
                                              destruct RHS eqn:H'; [ | reflexivity ]
                                         | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None, H : lookupb ?m (SVar ?k') = Some _ |- _ ]
                                           => rewrite Hm_small in H by omega
                                         | [ H : lookupb ?t ?m ?n = Some _, H' : lookupb ?t' ?m ?n = Some _ |- _ ]
                                           => let H'' := fresh in
                                              pose proof (@lookupb_unique_type _ _ _ _ SymbolicExprContextOk m n t t') as H'';
                                              rewrite H, H' in H'';
                                              specialize_by congruence;
                                              (subst t || subst t')
                                         | [ H : lookupb ?m ?s = Some ?k, H' : denote_symbolic_expr ?m _ ?s = Some ?k', Hm : forall t sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m t sv = Some v |- _ ]
                                           => let H'' := fresh in
                                              pose proof (Hm _ _ _ H) as H'';
                                              rewrite H' in H''; inversion_option;
                                              (subst k || subst k')
                                         | [ H : lookupb ?t ?m ?s = Some ?k, H' : denote_symbolic_expr ?m ?t' ?s = Some ?k', Hm : forall T sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m T sv = Some v |- _ ]
                                           => let H'' := fresh in
                                              let H''' := fresh in
                                              pose proof (Hm _ _ _ H) as H'';
                                              pose proof (denote_symbolic_expr_two_types m t t' s) as H''';
                                              rewrite H', H'' in H''';
                                              specialize_by congruence;
                                              (subst t || subst t')
                                         | [ |- denote_symbolic_expr ?m ?t ?e = Some ?v ]
                                           => lazymatch m with
                                              | extendb ?m' _ _
                                                => apply (fun pf1 => denote_symbolic_expr_weaken m' m pf1 t e v); [ intros ??? | ]
                                              end
                                         end ]
                        | repeat first [ progress cbn [denote_symbolic_expr fst snd projT1 projT2]
                                       | setoid_rewrite length_extendb
                                       | rewrite Nat.sub_diag
                                       | reflexivity
                                       | discriminate
                                       | rewrite eq_trans_sym_inv_r
                                       | progress simpl @nth_error
                                       | progress unfold var_cast;
                                         break_innermost_match
                                       | match goal with
                                         | [ H : context[flat_type_beq _ _ ?x ?x] |- _ ]
                                           => setoid_rewrite (flat_type_dec_lb _ _ base_type_code_lb x x eq_refl) in H
                                         end ] ].
        all:repeat match goal with
                   | [ H : SVar _ = SVar _ |- _ ] => inversion H; clear H
                   end.
        all:subst.
        all:try omega.
        all: try (intros; apply Hm_small; omega).
        all:destruct_head'_or.
        all:try (intro; progress destruct_head'_or).
        all:try solve [ repeat first [ progress subst
                                       | progress inversion_option
                                       | progress intros *
                                       | progress cbn [eq_rect eq_rec eq_ind]
                                       | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                                       | progress destruct_head'_or
                                       | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                                       | setoid_rewrite in_app_iff
                                       | break_innermost_match_step
                                       | progress simpl in *
                                       | discriminate
                                       | assumption
                                       | symmetry; assumption
                                       | reflexivity
                                       | progress intros
                                       | match goal with
                                         | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                                           => assert (a = b) by (clear -H H'; congruence);
                                              (subst a || subst b)
                                         | [ H : ?x <> ?x |- _ ] => exfalso; apply H; clear
                                         | [ H : lookupb ?t ?m ?n = Some _ |- None = @lookupb _ _ _ ?C ?t' ?m ?n ]
                                           => let H' := fresh in
                                              let RHS := match goal with |- _ = ?RHS => RHS end in
                                              destruct RHS eqn:H'; [ | reflexivity ]
                                         | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None, H : lookupb ?m (SVar ?k') = Some _ |- _ ]
                                           => rewrite Hm_small in H by omega
                                         | [ H : lookupb ?t ?m ?n = Some _, H' : lookupb ?t' ?m ?n = Some _ |- _ ]
                                           => let H'' := fresh in
                                              pose proof (@lookupb_unique_type _ _ _ _ SymbolicExprContextOk m n t t') as H'';
                                              rewrite H, H' in H'';
                                              specialize_by congruence;
                                              (subst t || subst t')
                                         | [ H : lookupb ?m ?s = Some ?k, H' : denote_symbolic_expr ?m _ ?s = Some ?k', Hm : forall t sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m t sv = Some v |- _ ]
                                           => let H'' := fresh in
                                              pose proof (Hm _ _ _ H) as H'';
                                              rewrite H' in H''; inversion_option;
                                              (subst k || subst k')
                                         | [ H : lookupb ?t ?m ?s = Some ?k, H' : denote_symbolic_expr ?m ?t' ?s = Some ?k', Hm : forall T sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m T sv = Some v |- _ ]
                                           => let H'' := fresh in
                                              let H''' := fresh in
                                              pose proof (Hm _ _ _ H) as H'';
                                              pose proof (denote_symbolic_expr_two_types m t t' s) as H''';
                                              rewrite H', H'' in H''';
                                              specialize_by congruence;
                                              (subst t || subst t')
                                         | [ |- denote_symbolic_expr ?m ?t ?e = Some ?v ]
                                           => lazymatch m with
                                              | extendb ?m' _ _
                                                => apply (fun pf1 => denote_symbolic_expr_weaken m' m pf1 t e v); [ intros ??? | ]
                                              end
                                         end ]
                        | repeat first [ progress cbn [denote_symbolic_expr fst snd projT1 projT2]
                                       | setoid_rewrite length_extendb
                                       | rewrite Nat.sub_diag
                                       | reflexivity
                                       | discriminate
                                       | rewrite eq_trans_sym_inv_r
                                       | progress simpl @nth_error
                                       | progress unfold var_cast;
                                         break_innermost_match
                                       | match goal with
                                         | [ H : context[flat_type_beq _ _ ?x ?x] |- _ ]
                                           => setoid_rewrite (flat_type_dec_lb _ _ base_type_code_lb x x eq_refl) in H
                                         end ] ].
        all:try lazymatch goal with
                | [ H : norm_symbolize_exprf _ = Some _ |- _ ]
                  => let H' := fresh in
                     refine (let H' := denote_symbolic_expr_norm_symbolize_exprf H _ in _); clearbody H';
                       specialize_by eauto;
                       move H' at bottom
                end.
        all:cbn [denote_symbolic_expr] in *.
        all:try match goal with |- _ <= _ -> _ => intro end.
        all:try match goal with
                | [ H : context[nth_error _ (?x - ?y)] |- _ ]
                  => rewrite (not_le_minus_0 x y) in H by omega
                end.
        move s0 at bottom.


        SearchAbout (_ - _ = 0).

        { eapply denote_symbolic_expr_flatten_binding_list; eauto.
                  all:try solve [ repeat first [ progress subst
                                       | progress inversion_option
                                       | progress intros *
                                       | progress cbn [eq_rect eq_rec eq_ind]
                                       | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                                       | progress destruct_head'_or
                                       | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                                       | setoid_rewrite in_app_iff
                                       | break_innermost_match_step
                                       | progress simpl in *
                                       | discriminate
                                       | assumption
                                       | symmetry; assumption
                                       | reflexivity
                                       | progress intros
                                       | match goal with
                                         | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                                           => assert (a = b) by (clear -H H'; congruence);
                                              (subst a || subst b)
                                         | [ H : ?x <> ?x |- _ ] => exfalso; apply H; clear
                                         | [ H : lookupb ?t ?m ?n = Some _ |- None = @lookupb _ _ _ ?C ?t' ?m ?n ]
                                           => let H' := fresh in
                                              let RHS := match goal with |- _ = ?RHS => RHS end in
                                              destruct RHS eqn:H'; [ | reflexivity ]
                                         | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None, H : lookupb ?m (SVar ?k') = Some _ |- _ ]
                                           => rewrite Hm_small in H by omega
                                         | [ H : lookupb ?t ?m ?n = Some _, H' : lookupb ?t' ?m ?n = Some _ |- _ ]
                                           => let H'' := fresh in
                                              pose proof (@lookupb_unique_type _ _ _ _ SymbolicExprContextOk m n t t') as H'';
                                              rewrite H, H' in H'';
                                              specialize_by congruence;
                                              (subst t || subst t')
                                         | [ H : lookupb ?m ?s = Some ?k, H' : denote_symbolic_expr ?m _ ?s = Some ?k', Hm : forall t sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m t sv = Some v |- _ ]
                                           => let H'' := fresh in
                                              pose proof (Hm _ _ _ H) as H'';
                                              rewrite H' in H''; inversion_option;
                                              (subst k || subst k')
                                         | [ H : lookupb ?t ?m ?s = Some ?k, H' : denote_symbolic_expr ?m ?t' ?s = Some ?k', Hm : forall T sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m T sv = Some v |- _ ]
                                           => let H'' := fresh in
                                              let H''' := fresh in
                                              pose proof (Hm _ _ _ H) as H'';
                                              pose proof (denote_symbolic_expr_two_types m t t' s) as H''';
                                              rewrite H', H'' in H''';
                                              specialize_by congruence;
                                              (subst t || subst t')
                                         | [ |- denote_symbolic_expr ?m ?t ?e = Some ?v ]
                                           => lazymatch m with
                                              | extendb ?m' _ _
                                                => apply (fun pf1 => denote_symbolic_expr_weaken m' m pf1 t e v); [ intros ??? | ]
                                              end
                                         end ]
                        | repeat first [ progress cbn [denote_symbolic_expr fst snd projT1 projT2]
                                       | setoid_rewrite length_extendb
                                       | rewrite Nat.sub_diag
                                       | reflexivity
                                       | discriminate
                                       | rewrite eq_trans_sym_inv_r
                                       | progress simpl @nth_error
                                       | progress unfold var_cast;
                                         break_innermost_match
                                       | match goal with
                                         | [ H : context[flat_type_beq _ _ ?x ?x] |- _ ]
                                           => setoid_rewrite (flat_type_dec_lb _ _ base_type_code_lb x x eq_refl) in H
                                         end ] ].
                  Focus 2.
                  { cbn [denote_symbolic_expr].


          repeat first [ progress subst
                       | progress inversion_option
                       | progress intros *
                       | progress cbn [eq_rect eq_rec eq_ind]
                       | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                       | progress destruct_head'_or
                       | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                       | setoid_rewrite in_app_iff
                       | break_innermost_match_step
                       | progress simpl in *
                       | discriminate
                       | assumption
                       | symmetry; assumption
                       | reflexivity
                       | progress intros
                       | match goal with
                         | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                           => assert (a = b) by (clear -H H'; congruence);
                              (subst a || subst b)
                         | [ H : ?x <> ?x |- _ ] => exfalso; apply H; clear
                         | [ H : lookupb ?t ?m ?n = Some _ |- None = @lookupb _ _ _ ?C ?t' ?m ?n ]
                           => let H' := fresh in
                              let RHS := match goal with |- _ = ?RHS => RHS end in
                              destruct RHS eqn:H'; [ | reflexivity ]
                         | [ Hm_small : forall t k, length ?m <= k -> lookupb ?m (SVar k) = None, H : lookupb ?m (SVar ?k') = Some _ |- _ ]
                           => rewrite Hm_small in H by omega
                         | [ H : lookupb ?t ?m ?n = Some _, H' : lookupb ?t' ?m ?n = Some _ |- _ ]
                           => let H'' := fresh in
                              pose proof (@lookupb_unique_type _ _ _ _ SymbolicExprContextOk m n t t') as H'';
                              rewrite H, H' in H'';
                              specialize_by congruence;
                              (subst t || subst t')
                         | [ H : lookupb ?m ?s = Some ?k, H' : denote_symbolic_expr ?m _ ?s = Some ?k', Hm : forall t sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m t sv = Some v |- _ ]
                           => let H'' := fresh in
                              pose proof (Hm _ _ _ H) as H'';
                              rewrite H' in H''; inversion_option;
                              (subst k || subst k')
                         | [ H : lookupb ?t ?m ?s = Some ?k, H' : denote_symbolic_expr ?m ?t' ?s = Some ?k', Hm : forall T sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m T sv = Some v |- _ ]
                           => let H'' := fresh in
                              let H''' := fresh in
                              pose proof (Hm _ _ _ H) as H'';
                              pose proof (denote_symbolic_expr_two_types m t t' s) as H''';
                              rewrite H', H'' in H''';
                              specialize_by congruence;
                              (subst t || subst t')
                         | [ |- denote_symbolic_expr ?m ?t ?e = Some ?v ]
                           => lazymatch m with
                              | extendb ?m' _ _
                                => apply (fun pf1 => denote_symbolic_expr_weaken m' m pf1 t e v); [ intros ??? | ]
                              end
                         end ].


                                  | match goal with
                                      | [ |- context[match eq_trans ?p (eq_sym ?p) with _ => _ end] ]
                                        => generalize p; unfold eq_sym
                                      end ] ].
                    SearchAbout (eq_trans _ (eq_sym _)).
                    simpl.
                    unfold var_cast.
                    break_innermost_match.
                    Focus 2.
                    destruct m.
                    { simpl in *.
                      setoid_rewrite (@lookupb_empty _ _ _ _ SymbolicExprContextOk) in Heqo0.
                      congruence. }
                    { unfold var_cast.
                      break_innermost_match.
                      move s at bottom.
                      unfold lookupb in *; simpl in *.
                      { break_innermost_match_hyps.
                        simpl in *.
                        move p at bottom.
                      unfold lookup
                    simpl @extendb.
                    SearchAbout (?x - ?x).
                    simpl.
            [ assumption | | eassumption ].
            simpl.
            Focus 2;
            eauto.
            eauto.
          move x at bottom.
          unfold symbolicify_smart_var in H2.
          simpl in H2.
          {
            match goal with
            | [ H : _ |- _ ] => apply H
            end.
            all:repeat first [ progress subst
                             | progress inversion_option
                             | progress intros *
                             | progress cbn [eq_rect eq_rec eq_ind]
                             | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                             | progress destruct_head'_or
                             | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                             | setoid_rewrite in_app_iff
                             | break_innermost_match_step
                             | progress simpl in *
                             | discriminate
                             | assumption
                             | symmetry; assumption
                             | reflexivity
                             | progress intros
                             | match goal with
                               | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                                 => assert (a = b) by (clear -H H'; congruence);
                                    (subst a || subst b)
                               | [ H : ?x <> ?x |- _ ] => exfalso; apply H; clear
                               | [ H : lookupb ?t ?m ?n = Some _ |- None = @lookupb _ _ _ ?C ?t' ?m ?n ]
                                 => let H' := fresh in
                                    let RHS := match goal with |- _ = ?RHS => RHS end in
                                    destruct RHS eqn:H'; [ | reflexivity ]
                               | [ H : lookupb ?t ?m ?n = Some _, H' : lookupb ?t' ?m ?n = Some _ |- _ ]
                                 => let H'' := fresh in
                                    pose proof (@lookupb_unique_type _ _ _ _ SymbolicExprContextOk m n t t') as H'';
                                    rewrite H, H' in H'';
                                    specialize_by congruence;
                                    (subst t || subst t')
                               | [ H : lookupb ?m ?s = Some ?k, H' : denote_symbolic_expr ?m _ ?s = Some ?k', Hm : forall t sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m t sv = Some v |- _ ]
                                 => let H'' := fresh in
                                    pose proof (Hm _ _ _ H) as H'';
                                    rewrite H' in H''; inversion_option;
                                    (subst k || subst k')
                               | [ H : lookupb ?t ?m ?s = Some ?k, H' : denote_symbolic_expr ?m ?t' ?s = Some ?k', Hm : forall T sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m T sv = Some v |- _ ]
                                 => let H'' := fresh in
                                    let H''' := fresh in
                                    pose proof (Hm _ _ _ H) as H'';
                                    pose proof (denote_symbolic_expr_two_types m t t' s) as H''';
                                    rewrite H', H'' in H''';
                                    specialize_by congruence;
                                    (subst t || subst t')
                               (*| [ |- denote_symbolic_expr ?m ?t ?e = _ ]
                                 => lazymatch m with
                                    | extendb ?m' _ _
                                      => etransitivity;
                                         [ apply (fun pf1 => denote_symbolic_expr_Proper m m' pf1 t e e eq_refl); intros ??
                                         | ]
                                    end*)
                               end ].
            all:repeat match goal with
                       | [ |- denote_symbolic_expr ?m ?t ?e = Some ?v ]
                         => lazymatch m with
                            | extendb ?m' _ _
                              => apply (fun pf1 => denote_symbolic_expr_weaken m' m pf1 t e v); [ intros ??? | ]
                            end
                       end.
            all:try solve [ repeat first [ progress subst
                             | progress inversion_option
                             | progress intros *
                             | progress cbn [eq_rect eq_rec eq_ind]
                             | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                             | progress destruct_head'_or
                             | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                             | setoid_rewrite in_app_iff
                             | break_innermost_match_step
                             | progress simpl in *
                             | discriminate
                             | assumption
                             | symmetry; assumption
                             | reflexivity
                             | progress intros
                             | match goal with
                               | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                                 => assert (a = b) by (clear -H H'; congruence);
                                    (subst a || subst b)
                               | [ H : ?x <> ?x |- _ ] => exfalso; apply H; clear
                               | [ H : lookupb ?t ?m ?n = Some _ |- None = @lookupb _ _ _ ?C ?t' ?m ?n ]
                                 => let H' := fresh in
                                    let RHS := match goal with |- _ = ?RHS => RHS end in
                                    destruct RHS eqn:H'; [ | reflexivity ]
                               | [ H : lookupb ?t ?m ?n = Some _, H' : lookupb ?t' ?m ?n = Some _ |- _ ]
                                 => let H'' := fresh in
                                    pose proof (@lookupb_unique_type _ _ _ _ SymbolicExprContextOk m n t t') as H'';
                                    rewrite H, H' in H'';
                                    specialize_by congruence;
                                    (subst t || subst t')
                               | [ H : lookupb ?m ?s = Some ?k, H' : denote_symbolic_expr ?m _ ?s = Some ?k', Hm : forall t sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m t sv = Some v |- _ ]
                                 => let H'' := fresh in
                                    pose proof (Hm _ _ _ H) as H'';
                                    rewrite H' in H''; inversion_option;
                                    (subst k || subst k')
                               | [ H : lookupb ?t ?m ?s = Some ?k, H' : denote_symbolic_expr ?m ?t' ?s = Some ?k', Hm : forall T sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m T sv = Some v |- _ ]
                                 => let H'' := fresh in
                                    let H''' := fresh in
                                    pose proof (Hm _ _ _ H) as H'';
                                    pose proof (denote_symbolic_expr_two_types m t t' s) as H''';
                                    rewrite H', H'' in H''';
                                    specialize_by congruence;
                                    (subst t || subst t')
                               (*| [ |- denote_symbolic_expr ?m ?t ?e = _ ]
                                 => lazymatch m with
                                    | extendb ?m' _ _
                                      => etransitivity;
                                         [ apply (fun pf1 => denote_symbolic_expr_Proper m m' pf1 t e e eq_refl); intros ??
                                         | ]
                                    end*)
                               end ] ]. } }
        {
            eapply ; eauto.
            Locate interpf_flatten_binding_list.


            pose interpf_flatten_binding_list.
            apply HG2.
            eauto using interpf_flatten_binding_list.
            all:repeat first [ progress subst
                             | progress inversion_option
                             | progress intros *
                             | progress cbn [eq_rect eq_rec eq_ind]
                             | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                             | progress destruct_head'_or
                             | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                             | setoid_rewrite in_app_iff
                             | break_innermost_match_step
                             | progress simpl in *
                             | discriminate
                             | assumption
                             | symmetry; assumption
                             | reflexivity
                             | progress intros
                             | match goal with
                               | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                                 => assert (a = b) by (clear -H H'; congruence);
                                    (subst a || subst b)
                               | [ H : ?x <> ?x |- _ ] => exfalso; apply H; clear
                               | [ H : lookupb ?t ?m ?n = Some _ |- None = @lookupb _ _ _ ?C ?t' ?m ?n ]
                                 => let H' := fresh in
                                    let RHS := match goal with |- _ = ?RHS => RHS end in
                                    destruct RHS eqn:H'; [ | reflexivity ]
                               | [ H : lookupb ?t ?m ?n = Some _, H' : lookupb ?t' ?m ?n = Some _ |- _ ]
                                 => let H'' := fresh in
                                    pose proof (@lookupb_unique_type _ _ _ _ SymbolicExprContextOk m n t t') as H'';
                                    rewrite H, H' in H'';
                                    specialize_by congruence;
                                    (subst t || subst t')
                               | [ H : lookupb ?m ?s = Some ?k, H' : denote_symbolic_expr ?m _ ?s = Some ?k', Hm : forall t sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m t sv = Some v |- _ ]
                                 => let H'' := fresh in
                                    pose proof (Hm _ _ _ H) as H'';
                                    rewrite H' in H''; inversion_option;
                                    (subst k || subst k')
                               | [ H : lookupb ?t ?m ?s = Some ?k, H' : denote_symbolic_expr ?m ?t' ?s = Some ?k', Hm : forall T sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m T sv = Some v |- _ ]
                                 => let H'' := fresh in
                                    let H''' := fresh in
                                    pose proof (Hm _ _ _ H) as H'';
                                    pose proof (denote_symbolic_expr_two_types m t t' s) as H''';
                                    rewrite H', H'' in H''';
                                    specialize_by congruence;
                                    (subst t || subst t')
                               (*| [ |- denote_symbolic_expr ?m ?t ?e = _ ]
                                 => lazymatch m with
                                    | extendb ?m' _ _
                                      => etransitivity;
                                         [ apply (fun pf1 => denote_symbolic_expr_Proper m m' pf1 t e e eq_refl); intros ??
                                         | ]
                                    end*)
                               end ].
            move H1 at bottom.
            lazymatch goal with
                               | [ H : lookupb ?t ?m ?s = Some ?k, H' : denote_symbolic_expr ?m ?t' ?s = Some ?k', Hm : forall t sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m t sv = Some v |- _ ]
                                 => let H'' := fresh in
                                    let H''' := fresh in
                                    pose proof (Hm _ _ _ H) as H'';
                                    pose proof (denote_symbolic_expr_two_types m t t' s) as H''';
                                    rewrite ?H', ?H'' in H''';
                                    specialize_by congruence;
                                    try (subst t || subst t')
                                      end.
            apply Hm in H4.
            all:admit. } }
              move m at bottom.
              move t0 at bottom.

          }

        {


            lazymatch goal with
            end.
                     lazymatch goal with
                     | [ |- lookupb (extendb ?m _ _) _ = lookupb ?m' _ ]
                       => unify m m'
                     end
                   | ]
            end.
              repeat first [ rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                           | progress subst
                           | break_innermost_match_step          match goal with
          | [ H : lookupb ?m ?s = Some ?k, H' : denote_symbolic_expr ?m _ ?s = Some ?k', Hm : forall t sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m t sv = Some v |- _ ]
            => let H'' := fresh in
               pose proof (Hm _ _ _ H) as H'';
                 rewrite H' in H''; inversion_option;
                   (subst k || subst k')
          end .
          solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ].
Focus 2.
          { eauto. lazymatch goal with
            | [ H : lookupb ?m ?s = Some ?k, H' : denote_symbolic_expr ?m _ ?s = Some ?k', Hm : forall t sv v, lookupb ?m sv = Some v -> denote_symbolic_expr ?m t sv = Some v |- _ ]
              => let H'' := fresh in
                 pose proof (Hm _ _ _ H) as H'';
                   rewrite H' in H''; inversion_option;
                     (subst k || subst k')
            end.

          { eapply HG2.
            eapply HGm.
            eassumption.
            match goal with
            end.
            move s at bottom.
            pose proof
          2:etransitivity;
            [ eapply denote_symbolic_expr_Proper;
              [ intros ?? | reflexivity ];
              lazymatch goal with
              | [ |- lookupb (extendb ?m _ _) _ = lookupb ?m' _ ]
                => unify m m'
              end;
              repeat first [ rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                           | progress subst
                           | progress simpl in *
                           | congruence
                           | break_innermost_match_step
                           | match goal with
                             | [ H : lookupb ?t ?m ?n = Some _ |- None = @lookupb _ _ _ ?C ?t' ?m ?n ]
                               => let H' := fresh in
                                  let RHS := match goal with |- _ = ?RHS => RHS end in
                                  destruct RHS eqn:H'; [ | reflexivity ]
                             | [ H : lookupb ?t ?m ?n = Some _, H' : lookupb ?t' ?m ?n = Some _ |- _ ]
                               => let H'' := fresh in
                                  pose proof (@lookupb_unique_type _ _ _ _ SymbolicExprContextOk m n t t') as H'';
                                  rewrite H, H' in H'';
                                  specialize_by congruence;
                                  (subst t || subst t')
                             end ]
            | ].
            | solve [ eauto ] ].

          { intros ??.
              instantiate (1:=m).

              break_innermost_match; subst; simpl; try congruence.
              lazymatch goal with
              end.
              congruence. }
            reflexivity.
            { eauto. } }
          Unfocus.
          Focus 2.
          {


              SearchAbout lookupb_removeb_different.
              Set Printing Implicit.
                reflexivity.
              rewrite look


          Focus 3.
          Focus 2.
          Focus 2.
          { right; eapply HGm; [ | eassumption ].

          2:eauto.
          2:
        Focus 2.
        { cbn [interpf interpf_step LetIn.Let_In].
          rewrite_hyp * by eauto.
          match goal with
          | [ H : _ |- _ ] => apply H
          end.
          all:intros *.
          all:try solve [ repeat first [ rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                         | setoid_rewrite in_app_iff
                         | progress subst
                         | progress simpl in *
                         | progress inversion_prod
                         | progress inversion_option
                         | progress destruct_head or
                         | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                         | progress intros ] ].
          Focus 3.
          { repeat first [ rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                         | setoid_rewrite in_app_iff
                         | progress subst
                         | progress simpl in *
                         | progress inversion_prod
                         | progress inversion_option
                         | progress destruct_head or
                         | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                         | progress intros
                         | match goal with
                           | [ H : nth_error ?ls (length ?ls) = Some _ |- _ ]
                             => rewrite (proj2 (nth_error_None _ _)) in H by reflexivity
                           end
                         | break_innermost_match_hyps_step
                         | break_innermost_match_step
                         | progress break_match_hyps ].
            Focus 4.
            { move m at bottom.
              destruct m; simpl in *; [ | congruence ].
              specialize_by_assumption.
              specialize (IHHwf nil).
              specialize_by_assumption.
              clear H2 Heqo0.
              clear Hm.
              simpl in *.
              clear HGm.
              move Heqo at bottom.
              unfold norm_symbolize_exprf in Heqo.
              move e1 at bottom.
              unfold option_map in
              move G at bottom.
              move G at bottom.
              unfold lookupb in Hm.
              unfold SymbolicExprContext in Hm.
              unfold AListContext in Hm.
              unfold find in Hm.
              clear Hm.
            SearchAbout (

            Set Printing Implicit.
            break_innermost_match_hyps.
          { repeat first [ rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                         | setoid_rewrite in_app_iff ].
                         |

          repeat first [
                       | setoid_rewrite in_app_iff
                       | progress break_innermost_match
                       | progress subst
                       | progress simpl in *
                       | progress inversion_prod
                       | progress inversion_option
                       | progress destruct_head or
                       | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                       | progress intros ].
          unfold LetIn.Let_In.
          simpl.
        match goal with
        | [ H : norm_symbolize_exprf _ = Some _ |- _ ]
        end
      { break_innermost_match.
        { apply H0.
        all:try match goal with
                | [ H : context[interpf interp_op (csef _ _)] |- _ ] => erewrite H; [ reflexivity | | eauto | eauto ]
                end;
          intros *;
          repeat first [ rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                       | setoid_rewrite in_app_iff
                       | progress break_innermost_match
                       | progress subst
                       | progress simpl in *
                       | progress inversion_prod
                       | progress inversion_option
                       | progress destruct_head or
                       | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                       | progress intros ].
        w
        3:rewrite_hyp !* by eauto.
        5:rewrite_hyp !* by eauto.
        6:rewrite_hyp !* by eauto.
        lazymatch goal with
        | [ Hm : forall t e1 e2 s v, symbolize_exprf _ = _ -> _, H' : symbolize_exprf _ = _ |- _ ]
                => erewrite (Hm _ _ _ _ _ H') by eassumption
              end.
            [ match goal with
              | [ Hm : forall t e1 e2 s v, symbolize_exprf _ = _ -> _, H' : symbolize_exprf _ = _ |- _ ]
                => erewrite (Hm _ _ _ _ _ H') by eassumption
              end
            | rewrite_hyp !* by eauto
            | rewrite_hyp !* by eauto ];
            match goal with
            | [ H : context[interpf interp_op (csef _ _)] |- _ ] => erewrite H; [ reflexivity | | eauto | eauto ]
            end;
            intros *;
            try solve [ repeat first [ rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                         | setoid_rewrite in_app_iff
                         | progress break_innermost_match
                         | progress subst
                         | progress simpl in *
                         | progress inversion_prod
                         | progress inversion_option
                         | progress destruct_head or
                         | solve [ eauto using interpf_flatten_binding_list, denote_symbolic_expr_flatten_binding_list ]
                         | progress intros ] ].
        admit.
        admit.
        admit. }*)
  Abort.

  Lemma interpf_prepend_prefix t e prefix
    : interpf interp_op (@prepend_prefix _ t e prefix) = interpf interp_op e.
  Proof.
    induction prefix; simpl; [ reflexivity | unfold LetIn.Let_In; assumption ].
  Qed.

  Lemma interp_cse prefix t e1 e2
        (Hwf : wf e1 e2)
    : forall x, interp interp_op (@cse interp_base_type prefix t e1 empty) x = interp interp_op e2 x.
  Proof.
    destruct Hwf; simpl; intros.
    etransitivity; [ | eapply interpf_prepend_prefix ].
    (*eapply interpf_csef; eauto;
      [ ..
      | eapply wff_prepend_prefix; [ .. | solve [ eauto ] ] ].
    { intros; eapply interpf_flatten_binding_list; eassumption. }
    { admit. }
    { admit. }*)
  Abort.

  Lemma InterpCSE t (e : Expr t)
        (prefix : forall var, list (sigT (fun t : flat_type => @exprf var t)))
        (*(Hlen : forall var1 var2, length (prefix var1) = length (prefix var2))
        (Hprefix : forall var1 var2 n t1 t2 e1 e2,
            nth_error (prefix var1) n = Some (existT _ t1 e1)
            -> nth_error (prefix var2) n = Some (existT _ t2 e2)
            -> exists pf : t1 = t2, wff nil (eq_rect _ exprf e1 _ pf) e2)*)
        (Hwf : Wf e)
    : forall x, Interp interp_op (@CSE t e prefix) x = Interp interp_op e x.
  Proof.
    admit; apply interp_cse; auto.
  Abort.
End symbolic.

Hint Rewrite @InterpCSE using solve_wf_side_condition : reflective_interp.
