(** * Common Subexpression Elimination for PHOAS Syntax *)
Require Import Coq.Lists.List.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.AListContext.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.ContextProperties.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Equality.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.WfProofs.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.CommonSubexpressionElimination.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Decidable.

Section symbolic.
  Context (base_type_code : Type)
          (op_code : Type)
          (base_type_code_beq : base_type_code -> base_type_code -> bool)
          (op_code_beq : op_code -> op_code -> bool)
          (base_type_code_bl : forall x y, base_type_code_beq x y = true -> x = y)
          (base_type_code_lb : forall x y, x = y -> base_type_code_beq x y = true)
          (op_code_bl : forall x y, op_code_beq x y = true -> x = y)
          (op_code_lb : forall x y, x = y -> op_code_beq x y = true)
          (op : flat_type base_type_code -> flat_type base_type_code -> Type)
          (symbolize_op : forall s d, op s d -> op_code).
  Local Notation symbolic_expr := (symbolic_expr base_type_code op_code).
  Context (normalize_symbolic_op_arguments : op_code -> symbolic_expr -> symbolic_expr)
          (inline_symbolic_expr_in_lookup : bool).

  Local Notation symbolic_expr_beq := (@symbolic_expr_beq base_type_code op_code base_type_code_beq op_code_beq).
  Local Notation symbolic_expr_lb := (@internal_symbolic_expr_dec_lb base_type_code op_code base_type_code_beq op_code_beq base_type_code_lb op_code_lb).
  Local Notation symbolic_expr_bl := (@internal_symbolic_expr_dec_bl base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op_code_bl).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).

  Local Notation symbolicify_smart_var := (@symbolicify_smart_var base_type_code op_code).
  Local Notation symbolize_exprf := (@symbolize_exprf base_type_code op_code op symbolize_op).
  Local Notation norm_symbolize_exprf := (@norm_symbolize_exprf base_type_code op_code op symbolize_op normalize_symbolic_op_arguments).
  Local Notation csef := (@csef base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op symbolize_op normalize_symbolic_op_arguments inline_symbolic_expr_in_lookup).
  Local Notation cse := (@cse base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op symbolize_op normalize_symbolic_op_arguments inline_symbolic_expr_in_lookup).
  Local Notation CSE := (@CSE base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op symbolize_op normalize_symbolic_op_arguments inline_symbolic_expr_in_lookup).
  Local Notation SymbolicExprContext := (@SymbolicExprContext base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl).
  Local Notation SymbolicExprContextOk := (@SymbolicExprContextOk base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl base_type_code_lb op_code_bl op_code_lb).
  Local Notation prepend_prefix := (@prepend_prefix base_type_code op).

  Local Instance base_type_code_dec : DecidableRel (@eq base_type_code)
    := dec_rel_of_bool_dec_rel base_type_code_beq base_type_code_bl base_type_code_lb.
  Local Instance op_code_dec : DecidableRel (@eq op_code)
    := dec_rel_of_bool_dec_rel op_code_beq op_code_bl op_code_lb.

  Section with_var.
    Context {var1 var2 : base_type_code -> Type}.

    Lemma wff_symbolize_exprf G t e1 e2
          (HG : forall t x y, List.In (existT _ t (x, y)) G -> snd x = snd y)
          (Hwf : wff G e1 e2)
      : @symbolize_exprf var1 t e1 = @symbolize_exprf var2 t e2.
    Proof.
      induction Hwf; simpl; erewrite_hyp ?* by eassumption; reflexivity.
    Qed.

    Lemma wff_norm_symbolize_exprf G t e1 e2
          (HG : forall t x y, List.In (existT _ t (x, y)) G -> snd x = snd y)
          (Hwf : wff G e1 e2)
      : @norm_symbolize_exprf var1 t e1 = @norm_symbolize_exprf var2 t e2.
    Proof.
      unfold norm_symbolize_exprf; erewrite wff_symbolize_exprf by eassumption; reflexivity.
    Qed.

    Section inline.
      Context (ctx : list symbolic_expr).
      Fixpoint inline_symbolic_expr (s : symbolic_expr) : symbolic_expr
        := match s with
           | STT => STT
           | SVar n => List.nth (List.length ctx - n) ctx (SVar n)
           | SOp argT op args => SOp argT op (inline_symbolic_expr args)
           | SPair x y => SPair (inline_symbolic_expr x) (inline_symbolic_expr y)
           | SFst A B x => SFst A B (inline_symbolic_expr x)
           | SSnd A B x => SSnd A B (inline_symbolic_expr x)
           | SInvalid => SInvalid
           end.

      Definition inline_existT (v : { t : _ & (var1 t * symbolic_expr) * (var2 t * symbolic_expr) }%type)
        : { t : _ & (var1 t * symbolic_expr) * (var2 t * symbolic_expr) }%type
        := let 'existT t ((v1, s1), (v2, s2)) := v in existT _ t ((v1, inline_symbolic_expr s1), (v2, inline_symbolic_expr s2)).
      Definition inline_ctx : list _ -> list _ := List.map inline_existT.

      Lemma inline_ctx_cons x xs : inline_ctx (x :: xs) = inline_existT x :: inline_ctx xs.
      Proof. reflexivity. Qed.
      Lemma inline_ctx_app : forall l1 l2, inline_ctx (l1 ++ l2) = inline_ctx l1 ++ inline_ctx l2.
      Proof. induction l1 as [|x xs IHxs], l2; simpl; rewrite ?IHxs; reflexivity. Qed.
    End inline.
    Global Arguments inline_existT {_} _, _ _.
    Global Arguments inline_ctx {_} _, _ _.

    Lemma In_inline {m G G'}
          (HGG' : forall t x x', List.In (existT _ t (x, x')) G -> List.In (existT _ t (fst x, fst x')) G')
      : forall t x x', List.In (inline_existT m (existT _ t (x, x'))) (inline_ctx m G)
                       -> List.In (existT _ t (fst x, fst x')) G'.
    Proof.
      intros t x x'; specialize (fun sx sx' => HGG' t (fst x, sx) (fst x', sx')).
      destruct x, x'; simpl in *.
      intro H; revert dependent G'; induction G as [|g G IHG]; intros; destruct H;
        simpl in *; unfold inline_existT in *; break_innermost_match_hyps;
          inversion_sigma; inversion_prod; subst; simpl in *.
      { eapply HGG'; left; reflexivity. }
      { apply IHG; auto; [].
        intros; eapply HGG'; right; eassumption. }
    Qed.

    Lemma map_fst_extendb {var} {c : @SymbolicExprContext (interp_flat_type var)} {t n} {v : interp_flat_type var t}
      : map fst (extendb c n v) = n :: map fst c.
    Proof. reflexivity. Qed.

    Local Arguments lookupb : simpl never.
    Local Arguments extendb : simpl never.
    Lemma wff_csef G G' t e1 e2
          (m1 : @SymbolicExprContext (interp_flat_type var1))
          (m2 : @SymbolicExprContext (interp_flat_type var2))
          m
          (Hm1_fst : List.map fst m1 = m)
          (Hm2_fst : List.map fst m2 = m)
          (Hlen : length m1 = length m2)
          (Hm1m2None : forall t v, lookupb t m1 v = None <-> lookupb t m2 v = None)
          (Hm1m2Some : forall t v sv1 sv2,
              lookupb t m1 v = Some sv1
              -> lookupb t m2 v = Some sv2
              -> forall k,
                  List.In k (flatten_binding_list
                               (t:=t)
                               (symbolicify_smart_var sv1 v)
                               (symbolicify_smart_var sv2 v))
                  -> List.In (inline_existT m k) (inline_ctx m G))
          (HG : forall t x y, List.In (existT _ t (x, y)) G -> snd x = snd y)
          (HGG' : forall t x x', List.In (existT _ t (x, x')) G -> List.In (existT _ t (fst x, fst x')) G')
          (Hwf : wff G e1 e2)
      : wff G' (@csef var1 t e1 m1) (@csef var2 t e2 m2).
    Proof.
      subst m; revert dependent m1; revert m2; revert dependent G'.
      induction Hwf; simpl; intros G' HGG' m2 m1 Hm1m2_fst Hlen Hm1m2None Hm1m2Some;
        pose proof (In_inline (m:=List.map fst m2) HGG') as HGG'_inline; move HGG'_inline at top;
          try constructor; auto.
      { erewrite wff_norm_symbolize_exprf by eassumption.
        break_innermost_match;
          try match goal with
              | [ H : lookupb ?m1 ?x = Some ?k, H' : lookupb ?m2 ?x = None |- _ ]
                => apply Hm1m2None in H'; congruence
              end;
          lazymatch goal with
          | [ |- wff _ (LetIn _ _) (LetIn _ _) ]
            => constructor; intros; auto; []
          | _ => idtac
          end;
          match goal with H : _ |- _ => apply H end.
        Set Ltac Profiling.
        all:try solve [ repeat first [ progress intros *
                                     | reflexivity
                                     | progress subst
                                     | progress inversion_option
                                     | match goal with |- context[lookupb (extendb _ _ _) _] => idtac end;
                                       rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                                     | match goal with |- context[List.In ?k (?x ++ ?y)] => idtac end;
                                       rewrite !in_app_iff
                                     | rewrite !inline_ctx_app
                                     | match goal with |- context[map fst (extendb _ _ _)] => idtac end;
                                       rewrite !map_fst_extendb
                                     | match goal with |- context[length (extendb _ _ _)] => idtac end;
                                       unfold SymbolicExprContext; rewrite !length_extendb
                                     | progress cbv beta delta [symbolize_var] in *
                                     | progress destruct_head'_or
                                     | progress cbn [fst snd projT1 projT2 eq_rect eq_rec eq_ind] in *
                                     | unfold inline_ctx; solve [ auto using in_map ]
                                     | match goal with
                                       | [ H : map fst _ = _ |- _ ] => rewrite H
                                       | [ H : length _ = _ |- _ ] => rewrite H
                                       | [ H : ?x = _, H' : context[?x] |- _ ] => rewrite H in H'
                                       | [ H : ?x <> ?x |- _ ] => exfalso; apply H; reflexivity
                                       end
                                     | match goal with |- _ \/ _ -> _ => idtac end;
                                       let H := fresh in intros [H|H]; eauto; revert H; []
                                     | progress intros
                                     | match goal with
                                       | [ H : List.In _ (flatten_binding_list (symbolicify_smart_var ?x1 ?v) (symbolicify_smart_var ?x2 ?v)) |- _ ]
                                         => solve [ destruct (flatten_binding_list_SmartVarfMap2_pair_In_split H); eauto ]
                                       | [ H : List.In _ (flatten_binding_list (symbolicify_smart_var ?x1 ?v) (symbolicify_smart_var ?x2 ?v)) |- _ ]
                                         => exact (flatten_binding_list_SmartVarfMap2_pair_same_in_eq2 H)
                                       end
                                     | break_innermost_match_step
                                     | break_innermost_match_hyps_step
                                     | apply conj ] ].
        all:intros *.
        all:rewrite ?(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk).
        all:try (progress break_innermost_match; subst; cbn [eq_rect eq_rec];
                 intros ??; inversion_option; subst).
        all:try solve [ repeat first [ progress intros *
                           | reflexivity
                           | progress subst
                           | progress cbn [fst snd projT1 projT2 eq_rect eq_rec eq_ind] in *
                           | progress inversion_option
                           | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                           | rewrite !in_app_iff
                           | rewrite !inline_ctx_app
                           | rewrite !map_fst_extendb
                           | unfold SymbolicExprContext; rewrite !length_extendb
                           | progress unfold symbolize_var in *
                           | progress destruct_head'_or
                           | unfold inline_ctx; solve [ auto using in_map ]
                           | match goal with
                             | [ H : map fst _ = _ |- _ ] => rewrite H
                             | [ H : length _ = _ |- _ ] => rewrite H
                             | [ H : ?x = _, H' : context[?x] |- _ ] => rewrite H in H'
                             | [ H : ?x <> ?x |- _ ] => exfalso; apply H; reflexivity
                             end
                           | match goal with |- _ \/ _ -> _ => idtac end;
                             let H := fresh in intros [H|H]; eauto; revert H; []
                           | progress intros
                           | match goal with
                             | [ H : List.In _ (flatten_binding_list (symbolicify_smart_var ?x1 ?v) (symbolicify_smart_var ?x2 ?v)) |- _ ]
                               => solve [ destruct (flatten_binding_list_SmartVarfMap2_pair_In_split H); eauto ]
                             | [ H : List.In _ (flatten_binding_list (symbolicify_smart_var ?x1 ?v) (symbolicify_smart_var ?x2 ?v)) |- _ ]
                               => exact (flatten_binding_list_SmartVarfMap2_pair_same_in_eq2 H)
                             end
                           | break_innermost_match_step
                           | break_innermost_match_hyps_step
                           | apply conj
                           | progress destruct_head'_sigT
                           | progress destruct_head'_prod ] ].
        Arguments inline_existT : clear implicits.
        { induction t.
          { simpl in *.
            intros ? [?| [] ].
            subst.
            simpl.
            rewrite inline_ctx_app.
            rewrite in_app_iff.
            Arguments inline_ctx : clear implicits.
            simpl.
        match goal with
        | [ Hm1m2Some : forall t v sv1 sv2, lookupb ?m1 _ = _ -> lookupb ?m2 _ = _ -> forall k, _ -> _,
              H1 : lookupb ?t' ?m1 ?v' = Some ?sv1',
              H2 : lookupb ?t' ?m2 ?v' = Some ?sv2'
              |- forall k', In k' _ -> _ ]
          => let H := fresh in
             let k := fresh k in
             intros k H;
               pose proof (Hm1m2Some t' v' sv1' sv2' H1 H2 k H)
        end.
        repeat first [ progress intros *
                     | reflexivity
                     | progress subst
                     | progress cbn [fst snd projT1 projT2 eq_rect eq_rec eq_ind] in *
                     | progress inversion_option
                     | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                     | rewrite !in_app_iff
                     | rewrite !inline_ctx_app
                     | rewrite !map_fst_extendb
                     | unfold SymbolicExprContext; rewrite !length_extendb
                     | progress unfold symbolize_var in *
                     | progress destruct_head'_or
                     | unfold inline_ctx; solve [ auto using in_map ]
                     | match goal with
                       | [ H : map fst _ = _ |- _ ] => rewrite H
                       | [ H : length _ = _ |- _ ] => rewrite H
                       | [ H : ?x = _, H' : context[?x] |- _ ] => rewrite H in H'
                       | [ H : ?x <> ?x |- _ ] => exfalso; apply H; reflexivity
                       end
                     | match goal with |- _ \/ _ -> _ => idtac end;
                       let H := fresh in intros [H|H]; eauto; revert H; []
                     | progress intros
                     | match goal with
                       | [ H : List.In _ (flatten_binding_list (symbolicify_smart_var ?x1 ?v) (symbolicify_smart_var ?x2 ?v)) |- _ ]
                         => solve [ destruct (flatten_binding_list_SmartVarfMap2_pair_In_split H); eauto ]
                       | [ H : List.In _ (flatten_binding_list (symbolicify_smart_var ?x1 ?v) (symbolicify_smart_var ?x2 ?v)) |- _ ]
                         => exact (flatten_binding_list_SmartVarfMap2_pair_same_in_eq2 H)
                       end
                     | break_innermost_match_step
                     | break_innermost_match_hyps_step
                     | apply conj ].
        Arguments inline_existT : clear implicits.
          right.
          unfold inline_existT in *.
          admit. }
          Set Printing Implicit.
                           | match goal with
                             end ] ].
          move Hm1m2Some at bottom.
          specialize (Hm1m2Some _ _ _ _ H3 H4).
          intro k; specialize (Hm1m2Some k).
          intro H'; specialize (Hm1m2Some H').
                    { progress unfold symbolize_var in *.
          unfold symbolize_var in *.

          left; apply Hm1m2Some.
          { .
          { auto.
          a
                           | apply conj ].
          move m1 at bottom.
          match goal with

          2:reflexivity.
          Show Ltac Profile.
          Focus 2.
          move x1 at bottom.
          Focus 2.
          Show Ltac Profile.
          all:try match goal with
                         | [ H : List.In _ (flatten_binding_list (symbolicify_smart_var ?x1 ?v) (symbolicify_smart_var ?x2 ?v)) |- _ ]
                           => solve [ destruct (flatten_binding_list_SmartVarfMap2_pair_In_split H); eauto ]
                  end.
          SearchAbout flatten_binding_list symbolicify_smart_var.

          solve [ unfold inline_ctx; eauto using in_map ].

          |
          unfold symbolize_var.
          Print symbolize_var.
          Focus 4.
          unfold extendb; simpl.
          Check @extendb.
                                              .
                           | rewrite].
          all:intros *.
          all:
          intros; apply H0; eauto.
        break_innermost_match;
          try match goal with
              | [ H : lookupb ?m1 ?x = Some ?k, H' : lookupb ?m2 ?x = None |- _ ]
                => apply Hm1m2None in H'; congruence
              end;
          lazymatch goal with
          | [ |- wff _ (LetIn _ _) (LetIn _ _) ]
            => constructor; intros; auto; []
          | _ => idtac
          end;
          match goal with H : _ |- _ => apply H end;
          try solve [ repeat first [ progress unfold symbolize_var
                       | rewrite Hlen
                       | progress subst
                       | progress inversion_option
                       | setoid_rewrite length_extendb
                       | setoid_rewrite List.in_app_iff
                       | setoid_rewrite inline_ctx_app
                       | setoid_rewrite inline_ctx_cons
                       | progress destruct_head' or
                       | solve [ unfold inline_ctx; eauto using in_map ]
                       | progress intros
                       | match goal with
                         | [ H : List.In _ (flatten_binding_list (symbolicify_smart_var ?x1 ?v) (symbolicify_smart_var ?x2 ?v)) |- _ ]
                           => solve [ destruct (flatten_binding_list_SmartVarfMap2_pair_In_split H); eauto ]
                         | [ H : List.In _ (flatten_binding_list (symbolicify_smart_var ?x1 ?v) (symbolicify_smart_var ?x2 ?v)) |- _ ]
                           => exact (flatten_binding_list_SmartVarfMap2_pair_same_in_eq2 H)
                         | [ H : context[lookupb (extendb _ _ _) _] |- _ ]
                           => rewrite (fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk) in H
                         end
                       | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                       | break_innermost_match_step
                       | break_innermost_match_hyps_step
                       | progress simpl in *
                       | solve [ intuition (eauto || congruence) ]
                       | match goal with
                         | [ H : forall t x y, _ |- _ ] => specialize (fun t x0 x1 y0 y1 => H t (x0, x1) (y0, y1)); cbn [fst snd] in H
                         | [ H : In (existT _ ?t (?x, ?x')) (flatten_binding_list (symbolicify_smart_var _ _) (symbolicify_smart_var _ _)),
                                 Hm1m2Some : forall t v sv1 sv2, _ -> _ -> forall k', In k' (flatten_binding_list _ _) -> In (inline_existT k') (inline_ctx ?G) |- _ ]
                           => is_var x; is_var x';
                              lazymatch goal with
                              | [ H : In (existT _ t ((fst x, _), (fst x', _))) G |- _ ] => fail
                              | _ => let H' := fresh in
                                     refine (let H' := flatten_binding_list_SmartVarfMap2_pair_in_generalize2 H _ _ in _);
                                     destruct H' as [? [? H']];
                                     eapply Hm1m2Some in H'; [ | eassumption.. ]
                              end
                         end ] ].
        { repeat first [ progress unfold symbolize_var
                       | rewrite Hlen
                       | progress subst
                       | progress inversion_option
                       | setoid_rewrite length_extendb
                       | setoid_rewrite List.in_app_iff
                       | setoid_rewrite inline_ctx_app
                       | setoid_rewrite inline_ctx_cons
                       | progress destruct_head' or
                       | solve [ unfold inline_ctx; eauto using in_map ]
                       | progress intros
                       | match goal with
                         | [ H : List.In _ (flatten_binding_list (symbolicify_smart_var ?x1 ?v) (symbolicify_smart_var ?x2 ?v)) |- _ ]
                           => solve [ destruct (flatten_binding_list_SmartVarfMap2_pair_In_split H); eauto ]
                         | [ H : List.In _ (flatten_binding_list (symbolicify_smart_var ?x1 ?v) (symbolicify_smart_var ?x2 ?v)) |- _ ]
                           => exact (flatten_binding_list_SmartVarfMap2_pair_same_in_eq2 H)
                         | [ H : context[lookupb (extendb _ _ _) _] |- _ ]
                           => rewrite (fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk) in H
                         end
                       | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                       | break_innermost_match_step
                       | break_innermost_match_hyps_step
                       | progress simpl in *
                       | solve [ intuition (eauto || congruence) ]
                       | match goal with
                         | [ H : forall t x y, _ |- _ ] => specialize (fun t x0 x1 y0 y1 => H t (x0, x1) (y0, y1)); cbn [fst snd] in H
                         | [ H : In (existT _ ?t (?x, ?x')) (flatten_binding_list (symbolicify_smart_var _ _) (symbolicify_smart_var _ _)),
                                 Hm1m2Some : forall t v sv1 sv2, _ -> _ -> forall k', In k' (flatten_binding_list _ _) -> In (inline_existT k') (inline_ctx ?G) |- _ ]
                           => is_var x; is_var x';
                              lazymatch goal with
                              | [ H : In (existT _ t ((fst x, _), (fst x', _))) G |- _ ] => fail
                              | _ => let H' := fresh in
                                     refine (let H' := flatten_binding_list_SmartVarfMap2_pair_in_generalize2 H _ _ in _);
                                     destruct H' as [? [? H']];
                                     eapply Hm1m2Some in H'; [ | eassumption.. ]
                              end
                         end ].
          { eapply HGG'_inline.
        {          repeat first [ progress unfold symbolize_var
                       | rewrite Hlen
                       | progress subst
                       | setoid_rewrite length_extendb
                       | setoid_rewrite inline_ctx_app
                       | setoid_rewrite inline_ctx_cons
                       | setoid_rewrite List.in_app_iff
                       | progress destruct_head' or
                       | solve [ eauto ]
                       | progress intros ].
                   repeat match goal with
                          | [ H : forall t x y, _ |- _ ] => specialize (fun t x0 x1 y0 y1 => H t (x0, x1) (y0, y1)); cbn [fst snd] in H
                          end.
                   { lazymatch goal with
                     end.
                     eauto.

                   unfold fst; break_innermost_match.
                   eapply (HGG'_inline _ (_, _) (_, _)).
                   move G at bottom.
                   match goal with
                   | [ H : forall
                   eapply (fun H1 H2 => Hm1m2Some _ _ _ _ H1 H2 (existT _ _ ((_, _), (_, _)))).
                   eauto.
                   match goal with
                   | [ H : List.In _ (flatten_binding_list (symbolicify_smart_var ?x1 ?v) (symbolicify_smart_var ?x2 ?v)) |- _ ]
                     => destruct (flatten_binding_list_SmartVarfMap2_pair_In_split H); eauto
                   end.
                   move G' at bottom.


        { repeat first
        Focus 7.
        { repeat first [ progress unfold symbolize_var
                       | rewrite Hlen
                       | progress subst
                       | progress inversion_option
                       | setoid_rewrite length_extendb
                       | setoid_rewrite List.in_app_iff
                       | setoid_rewrite inline_ctx_app
                       | setoid_rewrite inline_ctx_cons
                       | progress destruct_head' or
                       | solve [ unfold inline_ctx; eauto using in_map ]
                       | progress intros
                       | match goal with
                         | [ H : List.In _ (flatten_binding_list (symbolicify_smart_var ?x1 ?v) (symbolicify_smart_var ?x2 ?v)) |- _ ]
                           => solve [ destruct (flatten_binding_list_SmartVarfMap2_pair_In_split H); eauto ]
                         | [ H : List.In _ (flatten_binding_list (symbolicify_smart_var ?x1 ?v) (symbolicify_smart_var ?x2 ?v)) |- _ ]
                           => exact (flatten_binding_list_SmartVarfMap2_pair_same_in_eq2 H)
                         | [ H : context[lookupb (extendb _ _ _) _] |- _ ]
                           => rewrite (fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk) in H
                         end
                       | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                       | break_innermost_match_step
                       | break_innermost_match_hyps_step
                       | progress simpl in *
                       | solve [ intuition (eauto || congruence) ]
                       | match goal with
                         | [ H : forall t x y, _ |- _ ] => specialize (fun t x0 x1 y0 y1 => H t (x0, x1) (y0, y1)); cbn [fst snd] in H
                         | [ H : In (existT _ ?t (?x, ?x')) (flatten_binding_list (symbolicify_smart_var _ _) (symbolicify_smart_var _ _)),
                                 Hm1m2Some : forall t v sv1 sv2, _ -> _ -> forall k', In k' (flatten_binding_list _ _) -> In k' ?G |- _ ]
                           => is_var x; is_var x';
                              lazymatch goal with
                              | [ H : In (existT _ t ((fst x, _), (fst x', _))) G |- _ ] => fail
                              | _ => let H' := fresh in
                                     refine (let H' := flatten_binding_list_SmartVarfMap2_pair_in_generalize2 H _ _ in _);
                                     destruct H' as [? [? H']];
                                     eapply Hm1m2Some in H'; [ | eassumption.. ]
                              end
                         end ].
          { destruct_head'_sigT.
            destruct_head'_prod.
        { repeat first [ progress unfold symbolize_var
                       | rewrite Hlen
                       | progress subst
                       | progress inversion_option
                       | setoid_rewrite length_extendb
                       | setoid_rewrite List.in_app_iff
                       | setoid_rewrite inline_ctx_app
                       | setoid_rewrite inline_ctx_cons
                       | progress destruct_head' or
                       | solve [ unfold inline_ctx; eauto using in_map ]
                       | progress intros
                       | match goal with
                         | [ H : List.In _ (flatten_binding_list (symbolicify_smart_var ?x1 ?v) (symbolicify_smart_var ?x2 ?v)) |- _ ]
                           => solve [ destruct (flatten_binding_list_SmartVarfMap2_pair_In_split H); eauto ]
                         | [ H : List.In _ (flatten_binding_list (symbolicify_smart_var ?x1 ?v) (symbolicify_smart_var ?x2 ?v)) |- _ ]
                           => exact (flatten_binding_list_SmartVarfMap2_pair_same_in_eq2 H)
                         | [ H : context[lookupb (extendb _ _ _) _] |- _ ]
                           => rewrite (fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk) in H
                         end
                       | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                       | break_innermost_match_step
                       | break_innermost_match_hyps_step
                       | progress simpl in *
                       | solve [ intuition (eauto || congruence) ]
                       | match goal with
                         | [ H : forall t x y, _ |- _ ] => specialize (fun t x0 x1 y0 y1 => H t (x0, x1) (y0, y1)); cbn [fst snd] in H
                         | [ H : In (existT _ ?t (?x, ?x')) (flatten_binding_list (symbolicify_smart_var _ _) (symbolicify_smart_var _ _)),
                                 Hm1m2Some : forall t v sv1 sv2, _ -> _ -> forall k', In k' (flatten_binding_list _ _) -> In k' ?G |- _ ]
                           => is_var x; is_var x';
                              lazymatch goal with
                              | [ H : In (existT _ t ((fst x, _), (fst x', _))) G |- _ ] => fail
                              | _ => let H' := fresh in
                                     refine (let H' := flatten_binding_list_SmartVarfMap2_pair_in_generalize2 H _ _ in _);
                                     destruct H' as [? [? H']];
                                     eapply Hm1m2Some in H'; [ | eassumption.. ]
                              end
                         end ].
          lazymatch goal with
            | [ H : List.In _ (flatten_binding_list (symbolicify_smart_var ?x1 ?v) (symbolicify_smart_var ?x2 ?v)) |- _ ]
              => destruct (flatten_binding_list_SmartVarfMap2_pair_In_split H); eauto
            end.
          left.
        { repeat first [ progress unfold symbolize_var
                       | rewrite Hlen
                       | progress subst
                       | progress inversion_option
                       | setoid_rewrite length_extendb
                       | setoid_rewrite List.in_app_iff
                       | setoid_rewrite inline_ctx_app
                       | setoid_rewrite inline_ctx_cons
                       | progress destruct_head' or
                       | solve [ unfold inline_ctx; eauto using in_map ]
                       | progress intros
                       | match goal with
                         | [ H : List.In _ (flatten_binding_list (symbolicify_smart_var ?x1 ?v) (symbolicify_smart_var ?x2 ?v)) |- _ ]
                           => solve [ destruct (flatten_binding_list_SmartVarfMap2_pair_In_split H); eauto ]
                         | [ H : List.In _ (flatten_binding_list (symbolicify_smart_var ?x1 ?v) (symbolicify_smart_var ?x2 ?v)) |- _ ]
                           => exact (flatten_binding_list_SmartVarfMap2_pair_same_in_eq2 H)
                         | [ H : context[lookupb (extendb _ _ _) _] |- _ ]
                           => rewrite (fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk) in H
                         end
                       | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                       | break_innermost_match_step
                       | break_innermost_match_hyps_step
                       | progress simpl in *
                       | solve [ intuition (eauto || congruence) ]
                       | match goal with
                         | [ H : forall t x y, _ |- _ ] => specialize (fun t x0 x1 y0 y1 => H t (x0, x1) (y0, y1)); cbn [fst snd] in H
                         | [ H : In (existT _ ?t (?x, ?x')) (flatten_binding_list (symbolicify_smart_var _ _) (symbolicify_smart_var _ _)),
                                 Hm1m2Some : forall t v sv1 sv2, _ -> _ -> forall k', In k' (flatten_binding_list _ _) -> In k' ?G |- _ ]
                           => is_var x; is_var x';
                              lazymatch goal with
                              | [ H : In (existT _ t ((fst x, _), (fst x', _))) G |- _ ] => fail
                              | _ => let H' := fresh in
                                     refine (let H' := flatten_binding_list_SmartVarfMap2_pair_in_generalize2 H _ _ in _);
                                     destruct H' as [? [? H']];
                                     eapply Hm1m2Some in H'; [ | eassumption.. ]
                              end
                         end ].
          lazymatch goal with
          | [ H : In (existT _ ?t (?x, ?x')) (flatten_binding_list (symbolicify_smart_var _ _) (symbolicify_smart_var _ _)),
                  Hm1m2Some : forall t v sv1 sv2, _ -> _ -> forall k', In k' (flatten_binding_list _ _) -> In (inline_existT k') (inline_ctx ?G) |- _ ]
            => idtac end.
            => is_var x; is_var x';
                 lazymatch goal with
                 | [ H : In (existT _ t ((fst x, _), (fst x', _))) G |- _ ] => fail
                 | _ => let H' := fresh in
                        refine (let H' := flatten_binding_list_SmartVarfMap2_pair_in_generalize2 H _ _ in _);
                          destruct H' as [? [? H']];
                          eapply Hm1m2Some in H'; [ | eassumption.. ]
                 end
          end.
          lazymatch goal with
          | [ H : In (existT _ ?t (?x, ?x')) (flatten_binding_list (symbolicify_smart_var _ _) (symbolicify_smart_var _ _)),
                  Hm1m2Some : forall t v sv1 sv2, _ -> _ -> forall k', In k' (flatten_binding_list _ _) -> In k' ?G |- _ ]
            => is_var x; is_var x';
                 lazymatch goal with
                 | [ H : In (existT _ t ((fst x, _), (fst x', _))) G |- _ ] => fail
                 | _ => let H' := fresh in
                        refine (let H' := flatten_binding_list_SmartVarfMap2_pair_in_generalize2 H _ _ in _);
                          destruct H' as [? [? H']];
                          eapply Hm1m2Some in H'; [ | eassumption.. ]
                 end
          end.
lazymatch goal with
                         | [ H : List.In _ (flatten_binding_list (symbolicify_smart_var ?x1 ?v) (symbolicify_smart_var ?x2 ?v)) |- _ ]
                           => destruct (flatten_binding_list_SmartVarfMap2_pair_In_split H); eauto
end.
eauto.

                         | [ H : List.In _ (flatten_binding_list (symbolicify_smart_var ?x1 ?v) (symbolicify_smart_var ?x2 ?v)) |- _ ]
                           => exact (flatten_binding_list_SmartVarfMap2_pair_same_in_eq2 H)
                         | [ H : context[lookupb (extendb _ _ _) _] |- _ ]
                           => rewrite (fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk) in H
                         end          .
          SearchAbout (In (?f ?x) (List.map ?f ?ls)).
         repeat first [ progress unfold symbolize_var
                       | rewrite Hlen
                       | progress subst
                       | setoid_rewrite length_extendb
                       | setoid_rewrite List.in_app_iff
                       | progress destruct_head' or
                       | solve [ eauto ]
                       | progress intros ].
         repeat match goal with
                | [ H : context[lookupb (extendb _ _ _) _] |- _ ]
                  => rewrite (fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk) in H
                end.

         break_innermost_match_hyps; subst; cbn [eq_rect eq_rec eq_ind] in *; inversion_option; subst; auto.

         Focus 2.

         Check symbolicify_smart_var.
         left; assumption.
        end
         pose (@lookupb_extendb_full _ base_type_code_dec).
         rewrite (@lookupb_extendb_full in H1.
         (** FIXME: This actually isn't true, because the symbolic
             expr stored in G might not be the same as the one in the
             expression tree, when the one in the expression tree is a
             fresh var *)
         admit. }
    Admitted.

    Lemma wff_prepend_prefix {var1' var2'} prefix1 prefix2 G t e1 e2
          (Hlen : length prefix1 = length prefix2)
          (Hprefix : forall n t1 t2 e1 e2,
              nth_error prefix1 n = Some (existT _ t1 e1)
              -> nth_error prefix2 n = Some (existT _ t2 e2)
              -> exists pf : t1 = t2, wff nil (eq_rect _ exprf e1 _ pf) e2)
          (Hwf : wff G e1 e2)
      : wff G (@prepend_prefix var1' t e1 prefix1) (@prepend_prefix var2' t e2 prefix2).
    Proof.
      revert dependent G; revert dependent prefix2; induction prefix1, prefix2; simpl; intros Hlen Hprefix G Hwf; try congruence.
      { pose proof (Hprefix 0) as H0; specialize (fun n => Hprefix (S n)).
        destruct_head sigT; simpl in *.
        specialize (H0 _ _ _ _ eq_refl eq_refl); destruct_head ex; subst; simpl in *.
        constructor.
        { eapply wff_in_impl_Proper; [ eassumption | simpl; tauto ]. }
        { intros.
          apply IHprefix1; try congruence; auto.
          eapply wff_in_impl_Proper; [ eassumption | simpl; intros; rewrite in_app_iff; auto ]. } }
    Qed.

    Lemma wf_cse prefix1 prefix2 t e1 e2 (Hwf : wf e1 e2)
          (Hlen : length prefix1 = length prefix2)
          (Hprefix : forall n t1 t2 e1 e2,
              nth_error prefix1 n = Some (existT _ t1 e1)
              -> nth_error prefix2 n = Some (existT _ t2 e2)
              -> exists pf : t1 = t2, wff nil (eq_rect _ exprf e1 _ pf) e2)
      : wf (@cse var1 prefix1 t e1 empty) (@cse var2 prefix2 t e2 empty).
    Proof.
      destruct Hwf; simpl; constructor; intros.
      lazymatch goal with
      | [ |- wff (flatten_binding_list (t:=?src) ?x ?y) (csef _ (extendb _ ?n ?v)) (csef _ (extendb _ ?n' ?v')) ]
        => unify n n';
             apply wff_csef with (G:=flatten_binding_list (t:=src) (symbolicify_smart_var v n) (symbolicify_smart_var v' n'))
      end.
      { setoid_rewrite length_extendb; reflexivity. }
      { intros; rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk).
        break_innermost_match; subst; simpl; intuition (eauto || congruence). }
      { intros *; rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk).
        break_innermost_match; subst; simpl; try setoid_rewrite lookupb_empty; eauto using SymbolicExprContextOk; try congruence. }
      { intros *; intro H'; exact (flatten_binding_list_SmartVarfMap2_pair_same_in_eq2 H'). }
      { intros *; intro H'; destruct (flatten_binding_list_SmartVarfMap2_pair_In_split H'); eauto. }
      { apply wff_prepend_prefix; auto. }
    Qed.
  End with_var.

  Lemma Wf_CSE t (e : Expr t)
        (prefix : forall var, list (sigT (fun t : flat_type => @exprf var t)))
        (Hlen : forall var1 var2, length (prefix var1) = length (prefix var2))
        (Hprefix : forall var1 var2 n t1 t2 e1 e2,
            nth_error (prefix var1) n = Some (existT _ t1 e1)
            -> nth_error (prefix var2) n = Some (existT _ t2 e2)
            -> exists pf : t1 = t2, wff nil (eq_rect _ exprf e1 _ pf) e2)
        (Hwf : Wf e)
    : Wf (@CSE t e prefix).
  Proof.
    intros var1 var2; apply wf_cse; eauto.
  Qed.
End symbolic.

Hint Resolve Wf_CSE : wf.
