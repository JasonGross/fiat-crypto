Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.SetoidList.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Experiments.NewPipeline.LanguageInversion.
Require Import Crypto.Experiments.NewPipeline.LanguageWf.
Require Import Crypto.Experiments.NewPipeline.UnderLetsProofs.
Require Import Crypto.Experiments.NewPipeline.GENERATEDIdentifiersWithoutTypesProofs.
Require Import Crypto.Experiments.NewPipeline.Rewriter.
Require Import Crypto.Experiments.NewPipeline.RewriterWf1.
Require Import Crypto.Util.MSetPositive.Facts.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.CPSId.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.Tactics.TransparentAssert.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sigma.Related.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.SetoidList.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope bool_scope. Local Open Scope Z_scope.

Import EqNotations.
Module Compilers.
  Import Language.Compilers.
  Import LanguageInversion.Compilers.
  Import LanguageWf.Compilers.
  Import UnderLetsProofs.Compilers.
  Import GENERATEDIdentifiersWithoutTypesProofs.Compilers.
  Import Rewriter.Compilers.
  Import RewriterWf1.Compilers.
  Import expr.Notations.
  Import defaults.
  Import Rewriter.Compilers.RewriteRules.
  Import RewriterWf1.Compilers.RewriteRules.

  Module Import RewriteRules.
    Module Compile.
      Import Rewriter.Compilers.RewriteRules.Compile.
      Import RewriterWf1.Compilers.RewriteRules.Compile.

      Section with_var.
        Local Notation type_of_list
          := (fold_right (fun a b => prod a b) unit).
        Local Notation type_of_list_cps
          := (fold_right (fun a K => a -> K)).
        Context {ident var : type.type base.type -> Type}
                (eta_ident_cps : forall {T : type.type base.type -> Type} {t} (idc : ident t)
                                        (f : forall t', ident t' -> T t'),
                    T t)
                {pident : type.type pattern.base.type -> Type}
                (pident_arg_types : forall t, pident t -> list Type)
                (pident_unify pident_unify_unknown : forall t t' (idc : pident t) (idc' : ident t'), option (type_of_list (pident_arg_types t idc)))
                {raw_pident : Type}
                (strip_types : forall t, pident t -> raw_pident)
                (raw_pident_beq : raw_pident -> raw_pident -> bool)

                (full_types : raw_pident -> Type)
                (invert_bind_args invert_bind_args_unknown : forall t (idc : ident t) (pidc : raw_pident), option (full_types pidc))
                (type_of_raw_pident : forall (pidc : raw_pident), full_types pidc -> type.type base.type)
                (raw_pident_to_typed : forall (pidc : raw_pident) (args : full_types pidc), ident (type_of_raw_pident pidc args))
                (raw_pident_is_simple : raw_pident -> bool)
                (pident_unify_unknown_correct
                 : forall t t' idc idc', pident_unify_unknown t t' idc idc' = pident_unify t t' idc idc')
                (invert_bind_args_unknown_correct
                 : forall t idc pidc, invert_bind_args_unknown t idc pidc = invert_bind_args t idc pidc)
                (eta_ident_cps_correct : forall T t idc f, @eta_ident_cps T t idc f = f _ idc)
                (raw_pident_to_typed_invert_bind_args_type
                 : forall t idc p f, invert_bind_args t idc p = Some f -> t = type_of_raw_pident p f)
                (raw_pident_to_typed_invert_bind_args
                 : forall t idc p f (pf : invert_bind_args t idc p = Some f),
                    raw_pident_to_typed p f = rew [ident] raw_pident_to_typed_invert_bind_args_type t idc p f pf in idc).

        Local Notation type := (type.type base.type).
        Local Notation expr := (@expr.expr base.type ident var).
        Local Notation pattern := (@pattern.pattern pident).
        Local Notation UnderLets := (@UnderLets.UnderLets base.type ident var).
        Local Notation ptype := (type.type pattern.base.type).
        Local Notation value' := (@value' base.type ident var).
        Local Notation value := (@value base.type ident var).
        Local Notation value_with_lets := (@value_with_lets base.type ident var).
        Local Notation Base_value := (@Base_value base.type ident var).
        Local Notation splice_under_lets_with_value := (@splice_under_lets_with_value base.type ident var).
        Local Notation splice_value_with_lets := (@splice_value_with_lets base.type ident var).
        Local Notation rawexpr := (@rawexpr ident var).
        Local Notation eval_decision_tree := (@eval_decision_tree ident var raw_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple).
        Local Notation reveal_rawexpr_cps_gen := (@reveal_rawexpr_cps_gen ident var).
        Local Notation reveal_rawexpr_cps := (@reveal_rawexpr_cps ident var).
        Local Notation eval_rewrite_rules := (@eval_rewrite_rules ident var pident pident_arg_types pident_unify pident_unify_unknown raw_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple).
        Local Notation rewrite_rulesT := (@rewrite_rulesT ident var pident pident_arg_types).
        Local Notation rewrite_with_rule := (@rewrite_with_rule ident var pident pident_arg_types pident_unify pident_unify_unknown).
        Let type_base (t : base.type) : type := type.base t.
        Coercion type_base : base.type >-> type.

        Context (reify_and_let_binds_base_cps : forall (t : base.type), expr t -> forall T, (expr t -> UnderLets T) -> UnderLets T).

        Local Notation "e <---- e' ; f" := (splice_value_with_lets e' (fun e => f%under_lets)) : under_lets_scope.
        Local Notation "e <----- e' ; f" := (splice_under_lets_with_value e' (fun e => f%under_lets)) : under_lets_scope.
        Local Notation "e1 === e2" := (existT expr _ e1 = existT expr _ e2) : type_scope.

        Local Existing Instance SetoidList.eqlistA_equiv.

        Local Ltac rew_swap_list_step :=
          match goal with
          | [ H : swap_list ?a ?b ?ls1 = Some ?ls2, H' : context[swap_list ?a ?b ?ls2] |- _ ]
            => rewrite (swap_swap_list H) in H'
          | [ H : swap_list ?a ?b ?ls1 = Some ?ls2 |- context[swap_list ?a ?b ?ls2] ]
            => rewrite (swap_swap_list H)
          | [ H : swap_list ?a ?b ?ls1 = Some ?ls2 |- context[swap_list ?a ?b ?ls1] ]
            => rewrite H
          | [ H : swap_list ?a ?b ?ls1 = Some ?ls2,
                  H' : swap_list ?a ?b ?ls3 = Some ?ls4,
                       Hl : eqlistA ?R ?ls2 ?ls3
              |- _ ]
            => unique pose proof (swap_swap_list_eqlistA H H' Hl)
          end.

        Local Ltac rew_eval_decision_tree_step :=
          match goal with
          | [ H : (forall ctx' cont', eval_decision_tree ctx' ?d cont' = None \/ _)
              |- context[eval_decision_tree ?ctx ?d ?cont] ]
            => let H' := fresh in
               destruct (H ctx cont) as [H' | [? [? [H' ?] ] ] ]; rewrite H'
          end.

        Local Hint Constructors eqlistA.
        Local Hint Unfold rawexpr_equiv.
        Local Hint Unfold rawexpr_equiv_expr.

        Lemma eval_decision_tree_correct_Switch_cons
              {T} ctx icase icases app_case d cont
              (res := @eval_decision_tree T ctx (Switch (icase :: icases) app_case d) cont)
          : (exists b,
                res = match ctx with
                      | r :: ctx
                        => eval_decision_tree ctx (snd icase) (fun k ctx' => cont k (reveal_rawexpr_cps_gen (Some b) r _ id :: ctx'))
                      | _ => None
                      end)
            \/ res = eval_decision_tree ctx (Switch icases app_case d) cont
            \/ res = match app_case with
                     | Some app_case => eval_decision_tree ctx app_case cont
                     | None => None
                     end
            \/ res = eval_decision_tree ctx d cont.
        Proof using raw_pident_to_typed_invert_bind_args invert_bind_args_unknown_correct.
          destruct icase as [p icase]; subst res; cbn [fst snd].
          destruct ctx as [|r ctx]; [ now cbn; auto | ].
          destruct r.
          all: cbn [eval_decision_tree fold_right].
          all: destruct app_case as [app_case|].
          Set Ltac Profiling.
          Reset Ltac Profile.
          all: repeat first [ match goal with
                              | [ |- context[?x = ?x \/ _] ] => solve [ auto ]
                              | [ |- context[_ \/ ?x = ?x] ] => solve [ auto ]
                              | [ H : ?x = ?y |- context[?y = ?x \/ _] ] => solve [ auto ]
                              | [ H : ?y = ?x |- context[?x = ?y \/ _] ] => solve [ auto ]
                              | [ H : _ = ?v |- (exists b, ?v = _) \/ _ ]
                                => left; eexists; (idtac + symmetry); eassumption
                              | [ H : ?v = _ |- (exists b, ?v = _) \/ _ ]
                                => left; eexists; (idtac + symmetry); eassumption
                              | [ H : context[invert_bind_args_unknown ?a ?b ?c] |- _ ] => rewrite invert_bind_args_unknown_correct in H
                              | [ |- context[invert_bind_args_unknown ?a ?b ?c] ] => rewrite invert_bind_args_unknown_correct
                              | [ H : context[eval_decision_tree _ _ (fun _ _ => None)] |- _ ]
                                => rewrite eval_decision_tree_cont_None in H
                              | [ |- context[eval_decision_tree _ _ (fun _ _ => None)] ]
                                => rewrite eval_decision_tree_cont_None
                              | [ |- (exists b, ?f _ = ?f _) \/ _ ]
                                => left; eexists; reflexivity
                              end
                            | progress subst
                            | progress inversion_sigma
                            | progress inversion_option
                            | progress cbv [reveal_rawexpr_cps reveal_rawexpr_cps_gen value] in *
                            | progress cbn [value'] in *
                            | progress expr.invert_match
                            | break_match_hyps_step ltac:(fun v => is_var v; let t := type of v in unify t type)
                            | break_match_step ltac:(fun v => is_var v; let t := type of v in unify t type)
                            | match goal with
                              | [ |- context[match ?d with Failure => _ | _ => _ end] ] => is_var d; destruct d
                              end
                            | progress cbn [eq_rect Option.sequence Option.sequence_return] in *
                            | progress cbv [id option_bind' Option.bind Option.sequence Option.sequence_return] in *
                            | match goal with
                              | [ H : invert_bind_args _ _ _ = Some _ |- _ ]
                                => pose proof (@raw_pident_to_typed_invert_bind_args _ _ _ _ H);
                                   generalize dependent (@raw_pident_to_typed_invert_bind_args_type _ _ _ _ H); clear H; intros
                              | [ |- context[rew [?P] ?pf in ?v] ]
                                => lazymatch type of pf with
                                   | ?t1 = ?t2
                                     => generalize dependent v; generalize dependent pf;
                                        (generalize dependent t1 || generalize dependent t2);
                                        intros; subst
                                   end
                              | [ H : ?t = rew [?P] ?pf in ?v |- _ ]
                                => generalize dependent t; intros; subst
                              | [ H : context[rew [?P] ?pf in ?v] |- _ ]
                                => lazymatch type of pf with
                                   | ?t1 = ?t2
                                     => generalize dependent v; generalize dependent pf;
                                        (generalize dependent t1 || generalize dependent t2);
                                        intros; subst
                                   end
                              | [ |- context[match @fold_right ?A ?B ?f ?v ?ls with Some _ => _ | _ => _ end] ]
                                => destruct (@fold_right A B f v ls) eqn:?
                              end
                            | break_innermost_match_step ].
        Qed.

        Fixpoint eval_decision_tree_correct {T} d ctx cont
                 (res := @eval_decision_tree T ctx d cont)
                 {struct d}
          : res = None
            \/ exists n ctx',
              res = cont n ctx'
              /\ SetoidList.eqlistA rawexpr_equiv ctx ctx'.
        Proof using raw_pident_to_typed_invert_bind_args invert_bind_args_unknown_correct.
          specialize (eval_decision_tree_correct T).
          subst res; cbv zeta in *; destruct d.
          all: [ > specialize (eval_decision_tree_correct ltac:(assumption))
               | clear eval_decision_tree_correct
               |
               | specialize (eval_decision_tree_correct ltac:(assumption)) ].
          { cbn [eval_decision_tree]; cbv [Option.sequence]; break_innermost_match; eauto.
            all: right; repeat esplit; (idtac + symmetry); (eassumption + reflexivity). }
          { cbn; eauto. }
          { let d := match goal with d : decision_tree |- _ => d end in
            pose proof (eval_decision_tree_correct d) as eval_decision_tree_correct_default.
            let app_case := match goal with app_case : option decision_tree |- _ => app_case end in
            pose proof (match app_case return match app_case with Some _ => _ | _ => _ end with
                        | Some app_case => eval_decision_tree_correct app_case
                        | None => I
                        end) as eval_decision_tree_correct_app_case.
            let icases := match goal with icases : list (_ * decision_tree) |- _ => icases end in
            induction icases as [|icase icases IHicases];
              [ clear eval_decision_tree_correct | specialize (eval_decision_tree_correct (snd icase)) ].
            (* now that we have set up guardedness correctly, we can
               stop worrying so much about what order we destruct
               things in *)
            2: destruct (@eval_decision_tree_correct_Switch_cons _ ctx icase icases app_case d cont)
              as [ [? H] | [H| [H|H] ] ];
              rewrite H; try assumption.
            all: destruct app_case as [app_case|]; try (left; reflexivity).
            all: destruct ctx as [|ctx0 ctx]; [ try (left; reflexivity) | ].
            all: try destruct ctx0.
            all: cbn [eval_decision_tree fold_right]; cbv [reveal_rawexpr_cps reveal_rawexpr_cps_gen Option.sequence Option.sequence_return].
            all: repeat first [ rew_eval_decision_tree_step
                              | progress cbv [value id] in *
                              | progress cbn [value'] in *
                              | assumption
                              | reflexivity
                              | progress subst
                              | progress inversion_option
                              | expr.invert_match_step
                              | match goal with
                                | [ |- ?x = ?x \/ _ ] => left; reflexivity
                                | [ |- Some _ = None \/ _ ] => right
                                | [ |- None = Some _ \/ _ ] => right
                                | [ |- ?v = None \/ _ ]
                                  => lazymatch v with
                                     | match ?d with Failure => None | TryLeaf _ _ => None | _ => _ end
                                       => let H := fresh in
                                          assert (H : v = None) by (destruct d; auto); rewrite H
                                     | match ?d with Failure => ?x | TryLeaf _ _ => ?y | _ => _ end
                                       => let H := fresh in
                                          assert (H : v = x \/ v = y) by (destruct d; auto);
                                          destruct H as [H|H]; rewrite H
                                     end
                                | [ |- context[match ?x with nil => None | cons _ _ => _ end] ]
                                  => is_var x; destruct x
                                | [ |- match match ?x with nil => None | cons _ _ => _ end with None => None | Some _ => _ end = None \/ _ ]
                                  => is_var x; destruct x; [ left; reflexivity | ]
                                | [ |- _ \/ exists n ctx', ?f ?a ?b = ?f n ctx' /\ _ ]
                                  => right; exists a, b; split; [ reflexivity | ]
                                | [ |- exists n ctx', ?f ?a ?b = ?f n ctx' /\ _ ]
                                  => right; exists a, b; split; [ reflexivity | ]
                                | [ H : ?f ?a ?b = Some ?v |- exists n ctx', Some ?v = ?f n ctx' /\ _ ]
                                  => exists a, b; split; [ symmetry; assumption | ]
                                end
                              | break_match_hyps_step ltac:(fun v => is_var v; let t := type of v in unify t type)
                              | match goal with
                                | [ H : rawexpr_equiv ?a ?b |- eqlistA _ _ _ ] => unique assert (rawexpr_equiv b a) by (symmetry; exact H)
                                | [ H : eqlistA _ (_ :: _) _ |- eqlistA _ _ _ ] => inversion H; clear H; subst
                                | [ H : eqlistA _ nil _ |- eqlistA _ _ _ ] => inversion H; clear H; subst
                                | [ |- eqlistA _ (cons _ _) (cons _ _) ] => constructor
                                | [ |- eqlistA _ nil nil ] => constructor
                                | [ |- rawexpr_equiv _ _ ] => solve [ auto ]
                                | [ |- rawexpr_equiv (rValue ?v) ?r ] => change (rawexpr_equiv (rExpr v) r)
                                end
                              | break_innermost_match_step
                              | break_innermost_match_hyps_step ]. }
          { cbn [eval_decision_tree];
              repeat first [ rew_eval_decision_tree_step
                           | rew_swap_list_step
                           | solve [ eauto ]
                           | break_innermost_match_step ]. }
        Qed.

        Lemma eval_rewrite_rules_correct
              (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t))
              (maybe_do_again
               := fun (should_do_again : bool) (t : base.type)
                  => if should_do_again return ((@expr.expr base.type ident (if should_do_again then value else var) t) -> UnderLets (expr t))
                     then do_again t
                     else UnderLets.Base)
              (d : decision_tree)
              (rew_rules : rewrite_rulesT)
              (e : rawexpr)
              (res := @eval_rewrite_rules do_again d rew_rules e)
          : res = UnderLets.Base (expr_of_rawexpr e)
            \/ exists n pf e',
              nth_error rew_rules n = Some pf
              /\ Some res
                 = rewrite_with_rule do_again (expr_of_rawexpr e) e' pf
              /\ rawexpr_equiv e e'.
        Proof using raw_pident_to_typed_invert_bind_args invert_bind_args_unknown_correct.
          subst res; cbv [eval_rewrite_rules].
          refine (let H := eval_decision_tree_correct d [e] _ in _).
          destruct H as [H| [? [? [H ?] ] ] ]; rewrite H; cbn [Option.sequence Option.sequence_return];
            [ left; reflexivity | ]; clear H.
          inversion_head' eqlistA.
          unfold Option.bind at 1.
          break_innermost_match_step; [ | left; reflexivity ].
          cbn [Option.bind Option.sequence Option.sequence_return].
          match goal with
          | [ |- (Option.sequence_return ?x ?y) = _ \/ _ ]
            => destruct x eqn:?
          end; [ | left; reflexivity ]; cbn [Option.sequence_return].
          right; repeat esplit; try eassumption; auto.
        Qed.
      End with_var.

      Axiom proof_admitted : False.
      Local Notation admit := (match proof_admitted with end).

      Section with_interp.
        Local Notation type_of_list
          := (fold_right (fun a b => prod a b) unit).
        Local Notation type_of_list_cps
          := (fold_right (fun a K => a -> K)).
        Context {ident : type.type base.type -> Type}
                {ident_interp : forall t, ident t -> type.interp base.interp t}
                (eta_ident_cps : forall {T : type.type base.type -> Type} {t} (idc : ident t)
                                        (f : forall t', ident t' -> T t'),
                    T t)
                {pident : type.type pattern.base.type -> Type}
                (pident_arg_types : forall t, pident t -> list Type)
                (pident_unify pident_unify_unknown : forall t t' (idc : pident t) (idc' : ident t'), option (type_of_list (pident_arg_types t idc)))
                {raw_pident : Type}
                (strip_types : forall t, pident t -> raw_pident)
                (raw_pident_beq : raw_pident -> raw_pident -> bool)

                (full_types : raw_pident -> Type)
                (invert_bind_args invert_bind_args_unknown : forall t (idc : ident t) (pidc : raw_pident), option (full_types pidc))
                (type_of_raw_pident : forall (pidc : raw_pident), full_types pidc -> type.type base.type)
                (raw_pident_to_typed : forall (pidc : raw_pident) (args : full_types pidc), ident (type_of_raw_pident pidc args))
                (raw_pident_is_simple : raw_pident -> bool)
                (pident_unify_unknown_correct
                 : forall t t' idc idc', pident_unify_unknown t t' idc idc' = pident_unify t t' idc idc')
                (invert_bind_args_unknown_correct
                 : forall t idc pidc, invert_bind_args_unknown t idc pidc = invert_bind_args t idc pidc)
                (eta_ident_cps_correct : forall T t idc f, @eta_ident_cps T t idc f = f _ idc)
                (raw_pident_to_typed_invert_bind_args_type
                 : forall t idc p f, invert_bind_args t idc p = Some f -> t = type_of_raw_pident p f)
                (raw_pident_to_typed_invert_bind_args
                 : forall t idc p f (pf : invert_bind_args t idc p = Some f),
                    raw_pident_to_typed p f = rew [ident] raw_pident_to_typed_invert_bind_args_type t idc p f pf in idc)
                (pident_to_typed
                 : forall t idc (evm : EvarMap),
                    type_of_list (pident_arg_types t idc) -> ident (pattern.type.subst_default t evm))
                (ident_interp_Proper : forall t, Proper (eq ==> type.eqv) (@ident_interp t))
                (pident_unify_to_typed
                 : forall t t' idc idc' v,
                    pident_unify t t' idc idc' = Some v
                    -> forall evm pf,
                      rew [ident] pf in @pident_to_typed t idc evm v = idc').

        Local Notation var := (type.interp base.interp) (only parsing).
        Local Notation type := (type.type base.type).
        Local Notation expr := (@expr.expr base.type ident var).
        Local Notation pattern := (@pattern.pattern pident).
        Local Notation UnderLets := (@UnderLets.UnderLets base.type ident var).
        Local Notation ptype := (type.type pattern.base.type).
        Local Notation value' := (@value' base.type ident var).
        Local Notation value := (@value base.type ident var).
        Local Notation value_with_lets := (@value_with_lets base.type ident var).
        Local Notation Base_value := (@Base_value base.type ident var).
        Local Notation splice_under_lets_with_value := (@splice_under_lets_with_value base.type ident var).
        Local Notation splice_value_with_lets := (@splice_value_with_lets base.type ident var).
        Local Notation rawexpr := (@rawexpr ident var).
        Local Notation eval_decision_tree := (@eval_decision_tree ident var raw_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple).
        Local Notation eval_rewrite_rules := (@eval_rewrite_rules ident var pident pident_arg_types pident_unify pident_unify_unknown raw_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple).
        Local Notation rewrite_rulesT := (@rewrite_rulesT ident var pident pident_arg_types).
        Local Notation rewrite_with_rule := (@rewrite_with_rule ident var pident pident_arg_types pident_unify pident_unify_unknown).
        Local Notation reify := (@reify ident var).
        Local Notation reflect := (@reflect ident var).
        (*Local Notation rawexpr_equiv_expr := (@rawexpr_equiv_expr ident var).*)
        Local Notation rewrite_rule_data_interp_goodT := (@rewrite_rule_data_interp_goodT ident pident pident_arg_types pident_to_typed ident_interp).
        Local Notation rewrite_rules_interp_goodT := (@rewrite_rules_interp_goodT ident pident pident_arg_types pident_to_typed ident_interp).
        Local Notation rewrite_ruleTP := (@rewrite_ruleTP ident var pident pident_arg_types).
        Local Notation rewrite_ruleT := (@rewrite_ruleT ident var pident pident_arg_types).
        Local Notation unify_pattern := (@unify_pattern ident var pident pident_arg_types pident_unify pident_unify_unknown).
        Local Notation unify_pattern' := (@unify_pattern' ident var pident pident_arg_types pident_unify pident_unify_unknown).
        Local Notation under_with_unification_resultT_relation_hetero := (@under_with_unification_resultT_relation_hetero ident var pident pident_arg_types).
        Local Notation under_with_unification_resultT'_relation_hetero := (@under_with_unification_resultT'_relation_hetero ident var pident pident_arg_types).
        Local Notation assemble_identifier_rewriters := (@assemble_identifier_rewriters ident var eta_ident_cps pident pident_arg_types pident_unify pident_unify_unknown raw_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple).
        Local Notation assemble_identifier_rewriters' := (@assemble_identifier_rewriters' ident var pident pident_arg_types pident_unify pident_unify_unknown raw_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple).
        Local Notation pattern_default_interp' := (@pattern_default_interp' ident pident pident_arg_types pident_to_typed (@ident_interp)).
        Local Notation pattern_default_interp := (@pattern_default_interp ident pident pident_arg_types pident_to_typed (@ident_interp)).
        Local Notation pattern_collect_vars := (@pattern.collect_vars pident).
        Local Notation app_with_unification_resultT_cps := (@app_with_unification_resultT_cps pident pident_arg_types).
        Local Notation app_transport_with_unification_resultT'_cps := (@app_transport_with_unification_resultT'_cps pident pident_arg_types).
        Local Notation with_unification_resultT' := (@with_unification_resultT' pident pident_arg_types).
        Local Notation value'_interp := (@value'_interp ident ident_interp).
        Local Notation eval_decision_tree_correct := (@eval_decision_tree_correct ident var raw_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple invert_bind_args_unknown_correct raw_pident_to_typed_invert_bind_args_type raw_pident_to_typed_invert_bind_args).
        Local Notation expr_interp_related := (@expr.interp_related _ ident _ ident_interp).
        Local Notation UnderLets_interp_related := (@UnderLets.interp_related _ ident _ ident_interp _ _ expr_interp_related).
        Local Notation rawexpr_interp_related := (@rawexpr_interp_related ident ident_interp).
        Local Notation value_interp_related := (@value_interp_related ident ident_interp).
        Local Notation unification_resultT'_interp_related := (@unification_resultT'_interp_related ident pident pident_arg_types ident_interp).
        Local Notation unification_resultT_interp_related := (@unification_resultT_interp_related ident pident pident_arg_types ident_interp).
        Let type_base (t : base.type) : type := type.base t.
        Coercion type_base : base.type >-> type.

        Context (reify_and_let_binds_base_cps : forall (t : base.type), expr t -> forall T, (expr t -> UnderLets T) -> UnderLets T)
                (interp_reify_and_let_binds_base
                 : forall t e1 v1,
                    expr.interp ident_interp e1 == v1
                    -> expr.interp ident_interp (UnderLets.interp ident_interp (@reify_and_let_binds_base_cps t e1 _ UnderLets.Base)) == v1).

        Local Notation reify_and_let_binds_cps := (@reify_and_let_binds_cps ident var reify_and_let_binds_base_cps).
        Local Notation "e <---- e' ; f" := (splice_value_with_lets e' (fun e => f%under_lets)) : under_lets_scope.
        Local Notation "e <----- e' ; f" := (splice_under_lets_with_value e' (fun e => f%under_lets)) : under_lets_scope.

        Local Lemma pident_unify_to_typed'
          : forall t t' idc idc' v,
            pident_unify t t' idc idc' = Some v
            -> forall evm pf,
              @pident_to_typed t idc evm v = rew [ident] pf in idc'.
        Proof using pident_unify_to_typed.
          intros t t' idc idc' v H evm pf.
          pose proof (@pident_unify_to_typed t t' idc idc' v H evm (eq_sym pf)).
          subst; reflexivity.
        Qed.

        (*Local Infix "===" := expr_interp_related : type_scope.
        Local Infix "====" := value_interp_related : type_scope.
        Local Infix "=====" := rawexpr_interp_related : type_scope.*)

        Fixpoint types_match_with (evm : EvarMap) {t} (e : rawexpr) (p : pattern t) {struct p} : Prop
          := match p, e with
             | pattern.Wildcard t, e
               => pattern.type.subst t evm = Some (type_of_rawexpr e)
             | pattern.Ident t idc, rIdent known t' _ _ _
               => pattern.type.subst t evm = Some t'
             | pattern.App s d f x, rApp f' x' _ _
               => @types_match_with evm _ f' f
                  /\ @types_match_with evm _ x' x
             | pattern.Ident _ _, _
             | pattern.App _ _ _ _, _
               => False
             end.

        Lemma preunify_types_to_match_with {t re p evm}
          : match @preunify_types ident var pident t re p with
            | Some None => True
            | Some (Some (pt, t')) => pattern.type.subst pt evm = Some t'
            | None => False
            end
            -> types_match_with evm re p.
        Proof using Type.
          revert re; induction p; intro; cbn [preunify_types types_match_with];
            break_innermost_match; try exact id.
          all: repeat first [ progress Bool.split_andb
                            | progress type_beq_to_eq
                            | progress inversion_option
                            | progress Reflect.beq_to_eq
                                       (@type.type_beq pattern.base.type pattern.base.type.type_beq)
                                       (@type.internal_type_dec_bl pattern.base.type pattern.base.type.type_beq pattern.base.type.internal_type_dec_bl)
                                       (@type.internal_type_dec_lb pattern.base.type pattern.base.type.type_beq pattern.base.type.internal_type_dec_lb)
                            | progress subst
                            | reflexivity
                            | progress cbn [Option.bind pattern.type.subst_default pattern.type.subst]
                            | rewrite pattern.type.eq_subst_default_relax
                            | rewrite pattern.type.subst_relax
                            | match goal with
                              | [ H : (forall re, match preunify_types re ?p with _ => _ end -> _)
                                  |- context[preunify_types ?re' ?p] ]
                                => specialize (H re')
                              end
                            | break_innermost_match_hyps_step
                            | progress intros
                            | solve [ auto ]
                            | exfalso; assumption
                            | progress type.inversion_type
                            | progress cbv [Option.bind] in * ].
        Qed.

        Lemma unify_types_match_with {t re p evm}
          : @unify_types ident var pident t re p _ id = Some evm
            -> types_match_with evm re p.
        Proof using Type.
          intro H; apply preunify_types_to_match_with; revert H.
          cbv [unify_types id].
          break_innermost_match; intros; inversion_option; try exact I.
          RewriteRules.pattern.type.add_var_types_cps_id.
          cbv [option_type_type_beq] in *; break_innermost_match_hyps; type_beq_to_eq; inversion_option.
          let H := match goal with H : option_beq _ _ _ = true |- _ => H end in
          apply internal_option_dec_bl in H;
            [ | intros; type_beq_to_eq; assumption ].
          subst.
          assumption.
        Qed.

        Local Notation mk_new_evm0 evm ls
          := (fold_right
                (fun i k evm'
                 => k match PositiveMap.find i evm with
                      | Some v => PositiveMap.add i v evm'
                      | None => evm'
                      end) (fun evm' => evm')
                (List.rev ls)) (only parsing).

        Local Notation mk_new_evm evm ps
          := (mk_new_evm0
                evm
                (PositiveSet.elements ps)
                (PositiveMap.empty _)) (only parsing).

        Lemma types_match_with_Proper_evm {t p evm evm' re}
              (Hevm : forall k, PositiveSet.mem k (pattern_collect_vars p) = true -> PositiveMap.find k evm = PositiveMap.find k evm')
          : @types_match_with evm t re p <-> @types_match_with evm' t re p.
        Proof using Type.
          revert re; induction p, re; cbn [types_match_with pattern_collect_vars] in *.
          all: repeat first [ progress cbn [type_of_rawexpr] in *
                            | match goal with
                              | [ H : context[PositiveSet.mem _ (PositiveSet.union _ _)] |- _ ]
                                => setoid_rewrite PositiveSetFacts.union_b in H
                              | [ H : context[orb _ _ = true] |- _ ]
                                => setoid_rewrite Bool.orb_true_iff in H
                              end
                            | reflexivity
                            | progress split_contravariant_or
                            | progress specialize_by_assumption
                            | erewrite pattern.type.subst_eq_if_mem by eassumption
                            | match goal with
                              | [ H : _ |- _ ] => rewrite H by assumption
                              | [ |- (?x = Some ?y) <-> (?x' = Some ?y) ]
                                => cut (x = x'); [ let H := fresh in intro H; rewrite H; reflexivity | ]
                              end
                            | apply pattern.type.subst_eq_if_mem ].
        Qed.

        Lemma mem_pattern_collect_vars_types_match_with {evm t re p x}
              (H : @types_match_with evm t re p)
              (Hmem : PositiveSet.mem x (pattern_collect_vars p) = true)
          : PositiveMap.find x evm <> None.
        Proof using Type.
          revert re H; induction p; intros.
          all: repeat first [ progress cbn [pattern_collect_vars types_match_with] in *
                            | eapply pattern.type.mem_collect_vars_subst_Some_find; eassumption
                            | progress destruct_head'_and
                            | progress specialize_by_assumption
                            | assumption
                            | exfalso; assumption
                            | rewrite PositiveSetFacts.union_b, Bool.orb_true_iff in *
                            | progress destruct_head'_or
                            | break_innermost_match_hyps_step
                            | match goal with
                              | [ H : forall re, types_match_with ?evm re ?p -> _, H' : types_match_with ?evm _ ?p |- _ ] => specialize (H _ H')
                              end ].
        Qed.

        Lemma eq_type_of_rawexpr_of_unify_pattern' {t re p evm res}
              (H : @unify_pattern' t re p evm _ (@Some _) = Some res)
              (evm' := mk_new_evm evm (pattern_collect_vars p))
          : type_of_rawexpr re = pattern.type.subst_default t evm'.
        Proof using Type.
          subst evm'; revert re res H; generalize (PositiveMap.empty base.type).
          generalize (fun x => @PositiveSetFacts.In_elements_mem_iff x (pattern_collect_vars p)).
          setoid_rewrite List.in_rev.
          generalize (List.rev (PositiveSet.elements (pattern_collect_vars p))).
          induction p.
          all: repeat first [ progress intros
                            | progress cbn [pattern_collect_vars type_of_rawexpr unify_pattern'] in *
                            | progress inversion_option
                            | progress subst
                            | progress rewrite_type_transport_correct
                            | progress type_beq_to_eq
                            | break_innermost_match_hyps_step
                            | progress cbv [Option.bind] in *
                            | match goal with
                              | [ H : type_of_rawexpr ?re = _ |- type_of_rawexpr ?re = _ ]
                                => generalize dependent (type_of_rawexpr re); clear re
                              end ].
          Search pattern.type.subst_default.
          Search PositiveSet.elements.

        Lemma interp_unify_pattern' {t re p evm res v}
              (Hre : rawexpr_interp_related re v)
              (H : @unify_pattern' t re p evm _ (@Some _) = Some res)
              (evm' := mk_new_evm evm (pattern_collect_vars p))
              (Hty : type_of_rawexpr re = pattern.type.subst_default t evm')
          : exists resv : _,
              unification_resultT'_interp_related res resv
              /\ app_transport_with_unification_resultT'_cps
                   (pattern_default_interp' p evm' id) resv _ (@Some _)
                 = Some (rew Hty in v).
        Proof using pident_unify_unknown_correct pident_unify_to_typed.
          subst evm'; cbv [unification_resultT'_interp_related].
          revert re res v Hty H Hre; induction p; cbn [unify_pattern' related_unification_resultT' unification_resultT' rawexpr_interp_related app_transport_with_unification_resultT'_cps pattern_default_interp'] in *.
          all: repeat first [ progress intros
                            | rewrite pident_unify_unknown_correct in *
                            | progress cbv [Option.bind option_bind'] in *
                            | progress cbn [fst snd rawexpr_interp_related eq_rect] in *
                            | progress inversion_option
                            | progress destruct_head'_ex
                            | progress destruct_head'_and
                            | progress inversion_sigma
                            | progress subst
                            | progress eliminate_hprop_eq
                            | exfalso; assumption
                            | match goal with
                              | [ |- { x : _ | _ = x } ] => eexists; reflexivity
                              | [ |- exists x, _ = x /\ _ ] => eexists; split; [ reflexivity | ]
                              | [ |- exists x, _ /\ Some x = Some _ ] => eexists; split; [ | reflexivity ]
                              end
                            | progress cps_id'_with_option unify_pattern'_cps_id
                            | progress rewrite_type_transport_correct
                            | progress type_beq_to_eq
                            | rewrite app_lam_type_of_list
                            | break_innermost_match_hyps_step
                            | break_innermost_match_step
                            | match goal with
                              | [ H : forall re res v, _ = Some res -> rawexpr_interp_related _ _ -> _ |- _ ]
                                => specialize (H _ _ _ ltac:(eassumption) ltac:(eassumption))
                              | [ H : forall re res v Hty, _ = Some res -> rawexpr_interp_related _ _ -> _ |- _ ]
                                => specialize (fun Hty => H _ _ _ Hty ltac:(eassumption) ltac:(eassumption))
                              | [ |- exists x : _ * _, (_ /\ _) /\ _ ] => eexists (_, _); split; [ split; eassumption | ]
                              | [ |- exists res, value_interp_related (value_of_rawexpr _) res ]
                                => eexists; eapply value_of_rawexpr_interp_related; eassumption
                              | [ |- value_interp_related (value_of_rawexpr _) _ ]
                                => eapply value_of_rawexpr_interp_related; eassumption
                              | [ |- Some _ = Some _ ] => apply f_equal
                              end
                            | progress cbn [type_of_rawexpr expr.interp] in *
                            | erewrite pident_unify_to_typed' with (pf:=eq_refl) by eassumption
                            | progress cbv [eq_rect] in *
                            | progress fold (@with_unification_resultT') ].
          1-2:match goal with
              | [ H : ?x == ?y |- ?x = ?y ]
                => apply (type.eqv_iff_eq_of_funext (fun _ _ => functional_extensionality)), H
              end.
          move re2 at bottom.
          specialize (fun H => IHp1 (eq_trans (eq_sym x1) H)).
          cbn [pattern.type.subst_default] in *.
          specialize (fun H1 H2 => IHp1 (f_equal2 type.arrow H1 H2)).
          exact admit. (** FIXME: needs an assumption about deep type matching of evm to re *)
        Qed.

        Lemma interp_unify_pattern {t re p v res}
              (Hre : rawexpr_interp_related re v)
              (H : @unify_pattern t re p _ (@Some _) = Some res)
              (evm' := mk_new_evm (projT1 res) (pattern_collect_vars p))
              (Hty : type_of_rawexpr re = pattern.type.subst_default t evm')
          : exists resv : _,
            unification_resultT_interp_related res resv
            /\ (app_with_unification_resultT_cps (@pattern_default_interp t p) resv _ (@Some _) = Some (existT (fun evm => type.interp base.interp (pattern.type.subst_default t evm)) evm' (rew Hty in v))).
        Proof using pident_unify_unknown_correct pident_unify_to_typed.
          subst evm'; cbv [unify_pattern unification_resultT_interp_related unification_resultT related_unification_resultT app_with_unification_resultT_cps pattern_default_interp] in *.
          repeat first [ progress cbv [Option.bind related_sigT_by_eq] in *
                       | progress cbn [projT1 projT2 eq_rect] in *
                       | progress destruct_head'_ex
                       | progress destruct_head'_and
                       | progress inversion_option
                       | progress subst
                       | exfalso; assumption
                       | eassumption
                       | match goal with
                         | [ H : unify_pattern' _ _ _ _ _ = Some _ |- _ ]
                           => let T := type of H in
                              pose proof (H : id T) (* save an extra copy *);
                              eapply interp_unify_pattern' in H; [ | eassumption ]
                         | [ H : pattern.type.app_forall_vars (pattern.type.lam_forall_vars _) _ = Some _ |- _ ] => pose proof (pattern.type.app_forall_vars_lam_forall_vars H); clear H
                         | [ H : pattern.type.app_forall_vars (pattern.type.lam_forall_vars _) _ = None |- None = Some _ ]
                           => exfalso; revert H;
                              lazymatch goal with
                              | [ |- ?x = None -> False ]
                                => change (x <> None)
                              end;
                              rewrite app_lam_forall_vars_not_None_iff
                         end
                       | progress cps_id'_with_option unify_types_cps_id
                       | progress cps_id'_with_option unify_pattern'_cps_id
                       | progress cps_id'_with_option app_transport_with_unification_resultT'_cps_id
                       | break_innermost_match_hyps_step
                       | break_innermost_match_step
                       | match goal with
                         | [ |- exists x : sigT _, _ ] => eexists (existT _ _ _)
                         | [ |- { pf : _ = _ | _ } ] => exists eq_refl
                         | [ |- { pf : _ = _ & _ } ] => exists eq_refl
                         | [ |- _ /\ _ ] => split
                         | [ |- Some _ = Some _ ] => apply f_equal
                         | [ |- existT _ _ _ = existT _ _ _ ] => apply Sigma.path_sigT_uncurried
                         end
                       | break_match_step ltac:(fun _ => idtac)
                       | reflexivity
                       | match goal with
                         | [ H : unify_types _ _ _ _ = Some _ |- _ ] => apply unify_types_match_with in H
                         end
                       | progress intros
                       | eapply mem_pattern_collect_vars_types_match_with; eassumption ].
        Qed.

        Lemma interp_rewrite_with_rule
              (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t))
              (Hdo_again : forall G t e1 e2,
                  (forall t v1 v2, List.In (existT _ t (v1, v2)) G -> value'_interp v1 == v2)
                  -> expr.wf G e1 e2
                  -> expr.interp ident_interp (UnderLets.interp ident_interp (do_again t e1)) == expr.interp ident_interp e2)
              (rewr : rewrite_ruleT)
              (Hrewr : rewrite_rule_data_interp_goodT (projT2 rewr))
              t e re v1 v2
              (Ht : t = type_of_rawexpr re)
              (He : expr_interp_related e v2)
          : @rewrite_with_rule do_again t e re rewr = Some v1
            -> rawexpr_interp_related re (rew Ht in v2)
            -> UnderLets_interp_related v1 v2.
        Proof using pident_unify_to_typed pident_unify_unknown_correct.
          destruct rewr as [p r].
          cbv [rewrite_with_rule].
          repeat first [ match goal with
                         | [ |- Option.bind ?x _ = Some _ -> _ ]
                           => destruct x eqn:?; cbn [Option.bind]; [ | intros; solve [ inversion_option ] ]
                         end
                       | progress cps_id'_with_option unify_pattern_cps_id
                       | progress cps_id'_with_option app_with_unification_resultT_cps_id ].
          repeat first [ break_match_step ltac:(fun v => match v with Sumbool.sumbool_of_bool _ => idtac end)
                       | progress rewrite_type_transport_correct
                       | progress type_beq_to_eq
                       | progress cbv [option_bind'] in *
                       | progress cbn [Option.bind projT1 projT2 UnderLets.interp eq_rect UnderLets_interp_related] in *
                       | progress destruct_head'_sigT
                       | progress destruct_head'_sig
                       | progress inversion_option
                       | progress subst
                       | solve [ intros; inversion_option ]
                       | rewrite UnderLets_interp_related_splice_iff
                       | match goal with
                         | [ H : Option.bind ?x _ = Some _ |- _ ]
                           => destruct x eqn:?; cbn [Option.bind] in H; [ | solve [ inversion_option ] ]
                         | [ |- expr.interp _ (UnderLets.interp _ (maybe_do_again _ _ _ _)) == _ ]
                           => apply interp_maybe_do_again_gen; [ assumption | ]
                         | [ |- context[rew ?pf in _] ] => is_var pf; destruct pf
                         end ].
          repeat first [ progress destruct_head'_ex
                       | progress destruct_head'_sig
                       | progress destruct_head'_and
                       | exfalso; assumption
                       | progress inversion_option
                       | progress subst
                       | progress cbv [related_sigT_by_eq] in *
                       | progress cbn [projT1 projT2 eq_rect] in *
                       | match goal with
                         | [ H : unify_pattern _ _ _ _ = Some _ |- _ ] => eapply interp_unify_pattern in H; [ | eassumption ]
                         | [ H : unification_resultT_interp_related _ _, Hrewr : rewrite_rule_data_interp_goodT _ |- _ ]
                           => specialize (Hrewr _ _ H)
                         | [ H : option_eq _ ?x ?y, H' : ?x' = Some _ |- _ ]
                           => change x with x' in H; rewrite H' in H;
                              destruct y eqn:?; cbn [option_eq] in H
                         | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
                         | [ H : app_with_unification_resultT_cps _ _ _ (@Some _) = Some (existT _ ?evm _) |- _ ]
                           => is_var evm;
                              let H' := fresh in
                              pose proof (projT1_app_with_unification_resultT _ H) as H';
                              cbn [projT1] in H'; subst evm
                         end
                       | progress cbv [deep_rewrite_ruleTP_gen_good_relation] in *
                       | unshelve (eapply UnderLets.splice_interp_related_of_ex; eexists (fun x => rew _ in x), _; repeat apply conj;
                                   [ eassumption | intros | ]);
                         [ etransitivity; eassumption | .. ] ].
          set (k := rew_should_do_again r) in *.
          destruct r; cbv in k.
          let v := (eval cbv in k) in destruct v; subst k; cbn [maybe_do_again].
          Focus 2.
          { cbn in H0.
            cbn [UnderLets.splice].
            cbn [UnderLets.interp_related].
            cbv [eq_rect eq_trans].
            break_innermost_match.
            assumption. }
          Unfocus.
          Unshelve.
          Focus 2.
          { repeat first [ reflexivity
                         | progress cbn [eq_rect] in *
                         | progress intros
                         | progress eliminate_hprop_eq
                         | match goal with
                           | [ |- context[rew _ in rew _ in _] ]
                             => rewrite <- eq_trans_rew_distr
                           | [ |- context[rew ?pf in _] ]
                             => tryif is_var pf then fail else generalize pf
                           end ]. }
          Unfocus.
          exact admit.
          repeat first [ match goal with
                           | [ H : app_with_unification_resultT_cps _ _ _ (@Some _) = Some (existT _ ?evm _) |- _ ]
                             => is_var evm;
                                let H' := fresh in
                                pose proof (projT1_app_with_unification_resultT _ H) as H';
                                cbn [projT1] in H'; subst evm
                         end ].
          move re at bottom.
          { exact admit. }
          (*
            repeat first [ match goal with
                           | [ H : app_with_unification_resultT_cps _ _ _ (@Some _) = Some (existT _ ?evm _) |- _ ]
                             => is_var evm;
                                let H' := fresh in
                                pose proof (projT1_app_with_unification_resultT _ H) as H';
                                cbn [projT1] in H'; subst evm
                           end ].
etransitivity; symmetry; eassumption. } *)
        Qed.

        Lemma interp_eval_rewrite_rules
              (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t))
              (d : decision_tree)
              (rew_rules : rewrite_rulesT)
              (re : rawexpr) v
              (res := @eval_rewrite_rules do_again d rew_rules re)
              (Hdo_again : forall G t e1 e2,
                  (forall t v1 v2, List.In (existT _ t (v1, v2)) G -> value'_interp v1 == v2)
                  -> expr.wf G e1 e2
                  -> expr.interp ident_interp (UnderLets.interp ident_interp (do_again t e1)) == expr.interp ident_interp e2)
              (Hr : rawexpr_interp_related re v)
              (Hrew_rules : rewrite_rules_interp_goodT rew_rules)
          : UnderLets_interp_related res v.
        Proof using raw_pident_to_typed_invert_bind_args invert_bind_args_unknown_correct pident_unify_unknown_correct pident_unify_to_typed.
          subst res; cbv [eval_rewrite_rules].
          refine (let H := eval_decision_tree_correct d [re] _ in _).
          destruct H as [H| [? [? [H ?] ] ] ]; rewrite H; cbn [Option.sequence Option.sequence_return UnderLets_interp_related];
            [ now apply expr_of_rawexpr_interp_related | ]; clear H.
          inversion_head' eqlistA.
          unfold Option.bind at 1.
          break_innermost_match_step; [ | cbn [Option.sequence_return UnderLets_interp_related]; now apply expr_of_rawexpr_interp_related ].
          cbn [Option.bind Option.sequence Option.sequence_return UnderLets_interp_related].
          match goal with
          | [ |- ?R (Option.sequence_return ?x ?y) _ ]
            => destruct x eqn:Hinterp
          end; cbn [Option.sequence_return UnderLets.interp]; [ | now apply expr_of_rawexpr_interp_related ].
          unshelve (eapply interp_rewrite_with_rule; [ | | | eassumption | ]; try eassumption).
          { apply eq_type_of_rawexpr_equiv; assumption. }
          { eapply Hrew_rules, nth_error_In; rewrite <- sigT_eta; eassumption. }
          { apply expr_of_rawexpr_interp_related; assumption. }
          { apply rawexpr_interp_related_Proper_rawexpr_equiv; assumption. }
        Qed.

        Lemma interp_assemble_identifier_rewriters'
              (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t))
              (dt : decision_tree)
              (rew_rules : rewrite_rulesT)
              t re K
              (res := @assemble_identifier_rewriters' dt rew_rules do_again t re K)
              (Ht : type_of_rawexpr re = t)
              v
              (HK : K = (fun P v => rew [P] Ht in v))(*
                      /\ rew pf in value_of_rawexpr re = ev })*)
              (Hdo_again : forall G t e1 e2,
                  (forall t v1 v2, List.In (existT _ t (v1, v2)) G -> value'_interp v1 == v2)
                  -> expr.wf G e1 e2
                  -> expr.interp ident_interp (UnderLets.interp ident_interp (do_again t e1)) == expr.interp ident_interp e2)
              (Hrew_rules : rewrite_rules_interp_goodT rew_rules)
              (Hr : rawexpr_interp_related re v)
          : value_interp_related res (rew Ht in v).
        Proof using raw_pident_to_typed_invert_bind_args_type raw_pident_to_typed_invert_bind_args invert_bind_args_unknown_correct pident_unify_unknown_correct pident_unify_to_typed.
          subst K res.
          revert dependent re; induction t as [t|s IHs d IHd]; cbn [assemble_identifier_rewriters' value'_interp];
            intros; fold (@type.interp).
          { cbn [value_interp_related].
            destruct Ht; cbn [eq_rect].
            apply interp_eval_rewrite_rules; [ exact Hdo_again | | ]; assumption. }
          { cbn [value_interp_related].
            intros x1 x2 Hx.
            lazymatch goal with
            | [ |- context[assemble_identifier_rewriters' _ _ _ _ ?re ?K] ] => apply (IHd re eq_refl); clear IHd
            end.
            cbn [rawexpr_interp_related type.interp type_of_rawexpr].
            do 2 eexists.
            exists (eq_sym Ht).
            unshelve eexists.
            { clear; cbv [rValueOrExpr2 type_of_rawexpr]; destruct s; reflexivity. }
            repeat apply conj.
            all: repeat first [ instantiate (1:=ltac:(eassumption))
                              | match goal with
                                | [ |- expr_interp_related (rew [?P] ?H in ?v) ?ev ]
                                  => is_evar ev;
                                     refine (_ : expr_interp_related (rew [P] H in v) (rew [type.interp base.interp] H in _))
                                end
                              | assumption
                              | progress cbv [eq_sym eq_rect]
                              | break_innermost_match_step
                              | reflexivity
                              | apply expr_of_rawexpr_interp_related
                              | apply reify_interp_related ]. }
        Qed.

        Lemma interp_assemble_identifier_rewriters
              (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t))
              (d : decision_tree)
              (rew_rules : rewrite_rulesT)
              t idc
              (res := @assemble_identifier_rewriters d rew_rules do_again t idc)
              (Hdo_again : forall G t e1 e2,
                  (forall t v1 v2, List.In (existT _ t (v1, v2)) G -> value'_interp v1 == v2)
                  -> expr.wf G e1 e2
                  -> expr.interp ident_interp (UnderLets.interp ident_interp (do_again t e1)) == expr.interp ident_interp e2)
              (Hrew_rules : rewrite_rules_interp_goodT rew_rules)
          : value_interp_related res (ident_interp t idc).
        Proof using eta_ident_cps_correct raw_pident_to_typed_invert_bind_args_type raw_pident_to_typed_invert_bind_args invert_bind_args_unknown_correct pident_unify_unknown_correct ident_interp_Proper pident_unify_to_typed.
          subst res; cbv [assemble_identifier_rewriters].
          rewrite eta_ident_cps_correct.
          match goal with
          | [ |- ?R (assemble_identifier_rewriters' ?d ?rew_rules ?do_again ?t ?re' ?K) _ ]
            => apply interp_assemble_identifier_rewriters' with (re:=re') (Ht:=eq_refl)
          end.
          all: cbn [rawexpr_interp_related expr.interp].
          all: try solve [ reflexivity
                         | assumption ].
          repeat apply conj; try apply ident_interp_Proper; reflexivity.
        Qed.

(*
        Local Notation eval_decision_tree_correct := (@eval_decision_tree_correct ident var raw_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple invert_bind_args_unknown_correct raw_pident_to_typed_invert_bind_args_type raw_pident_to_typed_invert_bind_args).
        Lemma value_interp_related1_reify_of_wf {under_lets G t e1 re2}
              (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 == v2)
              (Hwf : expr.wf G (@reify under_lets t e1) re2)
          : e1 === expr.interp ident_interp re2.
        Proof using Type.
          revert under_lets G e1 re2 HG Hwf; induction t as [|s IHs d IHd];
            cbn [value_interp_related1 reify]; intros.
          { destruct under_lets; [ rewrite <- UnderLets.interp_to_expr | ].
            all: eapply expr.wf_interp_Proper_gen1; eassumption. }
          { fold (@reify) (@reflect) in *.
            expr.inversion_wf_one_constr.
            break_innermost_match_hyps; try tauto; [].
            expr.invert_subst.
            cbn [expr.interp].
            eapply IHd.
            Focus 2.
            Search expr.wf.
            2:eapply expr.wf_trans.
            {


        Lemma interp_splice_under_lets_with_value {T t} v k v2
          : k (UnderLets.interp ident_interp v) === v2
            -> @splice_under_lets_with_value T t v k === v2.
        Proof using Type.
          cbv [value_with_lets] in *.
          induction t as [|s IHs d IHd]; cbn [splice_under_lets_with_value value' value_interp_related1 type.related] in *; cbv [respectful];
            fold (@type.interp) in *; eauto.
          rewrite UnderLets.interp_splice; exact id.
        Qed.

        Lemma interp_splice_value_with_lets {t t'} v1 k1 v2 k2
          : v1 === v2
            -> (forall v1, v1 === v2 -> k1 v1 === k2)
            -> @splice_value_with_lets t t' v1 k1 === k2.
        Proof using Type.
          cbv [splice_value_with_lets]; break_innermost_match; auto; [].
          intros; apply interp_splice_under_lets_with_value; auto.
        Qed.

        Lemma interp_reify_and_let_binds {with_lets t v1 v2}
          : v1 === v2
            -> expr.interp ident_interp (UnderLets.interp ident_interp (@reify_and_let_binds_cps with_lets t v1 _ UnderLets.Base))
               == v2.
        Proof using interp_reify_and_let_binds_base.
          cbv [reify_and_let_binds_cps]; break_innermost_match;
            rewrite ?UnderLets.interp_splice; cbn [UnderLets.interp];
              try apply interp_reify; auto.
        Qed.
*)
      End with_interp.

      Section with_cast.
        Context (cast_outside_of_range : ZRange.zrange -> Z -> Z).
        Local Notation var := (type.interp base.interp).
        Local Notation ident_interp := (@ident.gen_interp cast_outside_of_range).
        Local Notation value_interp_related := (@value_interp_related ident (@ident_interp)).
        Local Notation expr_interp_related := (@expr.interp_related _ ident _ (@ident_interp)).

        Section with_rewrite_head.
          Context (rewrite_head : forall t (idc : ident t), value_with_lets t)
                  (interp_rewrite_head : forall t idc v, ident_interp idc == v -> value_interp_related (rewrite_head t idc) v).

          Lemma interp_rewrite_bottomup G {t e1 e2 v}
                (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> value_interp_related v1 v2)
                (Hwf : expr.wf G e1 e2)
                (He : expr_interp_related e2 v)
            : value_interp_related (@rewrite_bottomup var rewrite_head t e1) v.
          Proof using interp_rewrite_head.
            induction Hwf; cbn [rewrite_bottomup value_interp_related expr_interp_related] in *; auto.
            all: repeat first [ apply interp_Base_value
                              | progress cbn [value_interp_related1 type.related List.In eq_rect fst snd] in *
                              | progress cbv [respectful LetIn.Let_In] in *
                              | match goal with
                                | [ H : context[rewrite_bottomup] |- value_interp_related (@rewrite_bottomup _ _ _ _) _ ]
                                  => apply H; clear H
                                end
                              | solve [ eauto ]
                              | progress specialize_by_assumption
                              | progress intros
                              | progress inversion_sigma
                              | progress inversion_prod
                              | progress subst
                              | progress fold (@type.interp) in *
                              | progress destruct_head'_or
                              | rewrite UnderLets.interp_reify_and_let_binds_base
                              | eapply interp_splice_under_lets_with_value
                              | eapply interp_splice_value_with_lets
                              | apply interp_reflect
                              | apply interp_reify_and_let_binds ].
            Focus 2.
            eapply H0.
            Focus 2.
            eapply He.
            eapply eqv_of_value_interp_related
          Qed.
        End with_rewrite_head.

        Local Notation nbe := (@rewrite_bottomup var (fun t idc => reflect (expr.Ident idc))).

        Lemma interp_nbe G {t e1 e2}
              (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 === v2)
              (Hwf : expr.wf G e1 e2)
          : @nbe t e1 === expr.interp (@ident_interp) e2.
        Proof using Type.
          eapply interp_rewrite_bottomup; try eassumption.
          intros; apply interp_reflect; try now apply ident.gen_interp_Proper.
        Qed.

        Lemma interp_repeat_rewrite
              {rewrite_head fuel G t e1 e2}
              (retT := @repeat_rewrite _ rewrite_head fuel t e1 === expr.interp (@ident_interp) e2)
              (Hrewrite_head
               : forall do_again
                        (Hdo_again : forall G t e1 e2,
                            (forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 === v2)
                            -> expr.wf G e1 e2
                            -> expr.interp (@ident_interp) (UnderLets.interp (@ident_interp) (do_again t e1)) == expr.interp (@ident_interp) e2)
                        t idc,
                  @rewrite_head do_again t idc === ident_interp idc)
              (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 === v2)
              (Hwf : expr.wf G e1 e2)
          : retT.
        Proof using Type.
          subst retT.
          revert rewrite_head G t e1 e2 Hrewrite_head HG Hwf.
          induction fuel as [|fuel IH]; cbn [repeat_rewrite]; intros;
            apply interp_rewrite_bottomup with (G:=G); auto; intros;
              apply Hrewrite_head; auto; intros.
          { refine (@interp_nbe _ (type.base _) _ _ _ _); [ | eassumption ]; auto. }
          { refine (IH _ _ (type.base _) _ _ _ _ _); [ | | eassumption ]; auto. }
        Qed.

        Lemma interp_rewrite
              {rewrite_head fuel G t e1 e2}
              (retT := expr.interp (@ident_interp) (@rewrite _ rewrite_head fuel t e1) == expr.interp (@ident_interp) e2)
              (Hrewrite_head
               : forall do_again
                        (Hdo_again : forall G t e1 e2,
                            (forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 === v2)
                            -> expr.wf G e1 e2
                            -> expr.interp (@ident_interp) (UnderLets.interp (@ident_interp) (do_again t e1)) == expr.interp (@ident_interp) e2)
                        t idc,
                  @rewrite_head do_again t idc === ident_interp idc)
              (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 === v2)
              (Hwf : expr.wf G e1 e2)
          : retT.
        Proof using Type.
          subst retT; cbv [rewrite].
          eapply interp_reify, interp_repeat_rewrite; [ | | eassumption ]; auto.
        Qed.

        Lemma InterpRewrite
              {rewrite_head fuel t e}
              (retT := expr.Interp (@ident_interp) (@Rewrite rewrite_head fuel t e) == expr.Interp (@ident_interp) e)
              (Hrewrite_head
               : forall do_again
                        (Hdo_again : forall G t e1 e2,
                            (forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 === v2)
                            -> expr.wf G e1 e2
                            -> expr.interp (@ident_interp) (UnderLets.interp (@ident_interp) (do_again t e1)) == expr.interp (@ident_interp) e2)
                        t idc,
                  @rewrite_head _ do_again t idc === ident_interp idc)
              (Hwf : expr.Wf e)
          : retT.
        Proof using Type.
          subst retT; cbv [Rewrite expr.Interp].
          eapply interp_rewrite; eauto; cbn [List.In]; tauto.
        Qed.
      End with_cast.
    End Compile.
  End RewriteRules.
End Compilers.
