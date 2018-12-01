Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.SetoidList.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Experiments.NewPipeline.LanguageInversion.
Require Import Crypto.Experiments.NewPipeline.LanguageWf.
Require Import Crypto.Experiments.NewPipeline.UnderLetsProofs.
Require Import Crypto.Experiments.NewPipeline.GENERATEDIdentifiersWithoutTypesProofs.
Require Import Crypto.Experiments.NewPipeline.Rewriter.
Require Import Crypto.Experiments.NewPipeline.RewriterWf1.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.CPSId.
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
                (type_vars_of_pident : forall t, pident t -> list (type.type pattern.base.type))

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
        Local Notation eval_rewrite_rules := (@eval_rewrite_rules ident var pident pident_arg_types pident_unify pident_unify_unknown raw_pident type_vars_of_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple).
        Local Notation rewrite_rulesT := (@rewrite_rulesT ident var pident pident_arg_types type_vars_of_pident).
        Local Notation rewrite_with_rule := (@rewrite_with_rule ident var pident pident_arg_types pident_unify pident_unify_unknown type_vars_of_pident).
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
                (type_vars_of_pident : forall t, pident t -> list (type.type pattern.base.type))

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
        Local Notation eval_rewrite_rules := (@eval_rewrite_rules ident var pident pident_arg_types pident_unify pident_unify_unknown raw_pident type_vars_of_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple).
        Local Notation rewrite_rulesT := (@rewrite_rulesT ident var pident pident_arg_types type_vars_of_pident).
        Local Notation rewrite_with_rule := (@rewrite_with_rule ident var pident pident_arg_types pident_unify pident_unify_unknown type_vars_of_pident).
        Local Notation reify := (@reify ident var).
        Local Notation reflect := (@reflect ident var).
        (*Local Notation rawexpr_equiv_expr := (@rawexpr_equiv_expr ident var).*)
        Local Notation rewrite_rule_data_interp_goodT := (@rewrite_rule_data_interp_goodT ident pident pident_arg_types type_vars_of_pident pident_to_typed ident_interp).
        Local Notation rewrite_rules_interp_goodT := (@rewrite_rules_interp_goodT ident pident pident_arg_types type_vars_of_pident pident_to_typed ident_interp).
        Local Notation rewrite_ruleTP := (@rewrite_ruleTP ident var pident pident_arg_types type_vars_of_pident).
        Local Notation rewrite_ruleT := (@rewrite_ruleT ident var pident pident_arg_types type_vars_of_pident).
        Local Notation unify_pattern := (@unify_pattern ident var pident pident_arg_types pident_unify pident_unify_unknown).
        Local Notation unify_pattern' := (@unify_pattern' ident var pident pident_arg_types pident_unify pident_unify_unknown).
        Local Notation under_with_unification_resultT_relation_hetero := (@under_with_unification_resultT_relation_hetero ident var pident pident_arg_types type_vars_of_pident).
        Local Notation under_with_unification_resultT'_relation_hetero := (@under_with_unification_resultT'_relation_hetero ident var pident pident_arg_types).
        Local Notation assemble_identifier_rewriters := (@assemble_identifier_rewriters ident var eta_ident_cps pident pident_arg_types pident_unify pident_unify_unknown raw_pident type_vars_of_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple).
        Local Notation assemble_identifier_rewriters' := (@assemble_identifier_rewriters' ident var pident pident_arg_types pident_unify pident_unify_unknown raw_pident type_vars_of_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple).
        Local Notation pattern_default_interp' := (@pattern_default_interp' ident pident pident_arg_types pident_to_typed).
        Local Notation pattern_default_interp := (@pattern_default_interp ident pident pident_arg_types type_vars_of_pident pident_to_typed).
        Local Notation ident_collect_vars := (@ident_collect_vars pident type_vars_of_pident).
        Local Notation pattern_collect_vars := (@pattern.collect_vars pident ident_collect_vars).
        Local Notation app_with_unification_resultT_cps := (@app_with_unification_resultT_cps ident var pident pident_arg_types type_vars_of_pident).
        Local Notation app_transport_with_unification_resultT'_cps := (@app_transport_with_unification_resultT'_cps ident var pident pident_arg_types).
        Local Notation with_unification_resultT' := (@with_unification_resultT' ident var pident pident_arg_types).
        Local Notation value_interp_ok := (@value_interp_ok ident ident_interp).
        Local Notation value_or_expr_interp_ok := (@value_or_expr_interp_ok ident ident_interp).
        Local Notation value'_interp := (@value'_interp ident ident_interp).
        Local Notation rawexpr_interp_ok := (@rawexpr_interp_ok ident ident_interp).
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

        Fixpoint expr_interp_related {t} (e : expr t) : type.interp base.interp t -> Prop
          := match e in expr.expr t return type.interp base.interp t -> Prop with
             | expr.Var t v1 => fun v2 => v1 == v2
             | expr.App s d f x
               => fun v2
                  => exists fv xv,
                      @expr_interp_related _ f fv
                      /\ @expr_interp_related _ x xv
                      /\ fv xv = v2
             | expr.Ident t idc
               => fun v2 => ident_interp _ idc == v2
             | expr.Abs s d f1
               => fun f2
                  => forall x1 x2,
                      x1 == x2
                      -> @expr_interp_related d (f1 x1) (f2 x2)
             | expr.LetIn s d x f
               => fun v2
                  => exists xv,
                      @expr_interp_related _ x xv
                      /\ @expr_interp_related d (f xv) v2 (* ? *)
             end.

        Fixpoint UnderLets_interp_related {T1 T2} (R : T1 -> T2 -> Prop) (e : UnderLets T1) (v2 : T2) : Prop
          := match e with
             | UnderLets.Base v1 => R v1 v2
             | UnderLets.UnderLet t e f
               => exists ev,
                  @expr_interp_related _ e ev
                  /\ @UnderLets_interp_related T1 T2 R (f ev) v2
             end.

        Lemma UnderLets_interp_related_to_expr_iff {t e v}
          : UnderLets_interp_related (@expr_interp_related t) e v
            <-> expr_interp_related (UnderLets.to_expr e) v.
        Proof using Type.
          induction e; cbn [UnderLets.to_expr UnderLets_interp_related expr_interp_related]; try reflexivity.
          match goal with H : _ |- _ => setoid_rewrite H end.
          reflexivity.
        Qed.

        Fixpoint value_interp_related {t with_lets} : @value' with_lets t -> type.interp base.interp t -> Prop
          := match t, with_lets with
             | type.base _, true => UnderLets_interp_related expr_interp_related
             | type.base _, false => expr_interp_related
             | type.arrow s d, _
               => fun (f1 : @value' _ s -> @value' _ d) (f2 : type.interp _ s -> type.interp _ d)
                  => forall x1 x2,
                      @value_interp_related s _ x1 x2
                      -> @value_interp_related d _ (f1 x1) (f2 x2)
             end.

        Fixpoint rawexpr_interp_related (r1 : rawexpr) : type.interp base.interp (type_of_rawexpr r1) -> Prop
          := match r1 return type.interp base.interp (type_of_rawexpr r1) -> Prop with
             | rExpr _ e1
             | rValue (type.base _) e1
               => expr_interp_related e1
             | rValue t1 v1
               => value_interp_related v1
             | rIdent _ t1 idc1 t'1 alt1
               => fun v2
                  => expr.interp ident_interp alt1 == v2
                     /\ existT expr t1 (expr.Ident idc1) = existT expr t'1 alt1
             | rApp f1 x1 t1 alt1
               => match alt1 in expr.expr t return type.interp base.interp t -> Prop with
                  | expr.App s d af ax
                    => fun v2
                       => exists fv xv (pff : type.arrow s d = type_of_rawexpr f1) (pfx : s = type_of_rawexpr x1),
                           @expr_interp_related _ af fv
                           /\ @expr_interp_related _ ax xv
                           /\ @rawexpr_interp_related f1 (rew pff in fv)
                           /\ @rawexpr_interp_related x1 (rew pfx in xv)
                           /\ fv xv = v2
                  | _ => fun _ => False
                  end
             end.

        Local Infix "===" := expr_interp_related : type_scope.
        Local Infix "====" := value_interp_related : type_scope.
        Local Infix "=====" := rawexpr_interp_related : type_scope.

        Fixpoint reify_interp_related {t with_lets} v1 v2 {struct t}
          : @value_interp_related t with_lets v1 v2
            -> expr_interp_related (reify v1) v2
        with reflect_interp_related {t with_lets} e1 v2 {struct t}
             : expr_interp_related e1 v2
               -> @value_interp_related t with_lets (reflect e1) v2.
        Proof using Type.
          all: destruct t as [|s d];
            [ clear reify_interp_related reflect_interp_related
            | pose proof (reify_interp_related s false) as reify_interp_related_s;
              pose proof (reflect_interp_related s false) as reflect_interp_related_s;
              pose proof (reify_interp_related d true) as reify_interp_related_d;
              pose proof (reflect_interp_related d true) as reflect_interp_related_d;
              clear reify_interp_related reflect_interp_related ].
          all: repeat first [ progress cbn [reify reflect] in *
                            | progress fold (@reify) (@reflect) in *
                            | progress cbn [expr_interp_related value_interp_related] in *
                            | break_innermost_match_step
                            | rewrite <- UnderLets_interp_related_to_expr_iff
                            | exact id
                            | assumption
                            | solve [ eauto ]
                            | progress intros
                            | match goal with H : _ |- _ => apply H; clear H end
                            | progress repeat esplit ].
        Qed.

        Lemma expr_of_rawexpr_interp_related r v
          : rawexpr_interp_related r v
            -> expr_interp_related (expr_of_rawexpr r) v.
        Proof using Type.
          revert v; induction r; cbn [expr_of_rawexpr expr_interp_related rawexpr_interp_related]; intros.
          all: repeat first [ progress destruct_head'_and
                            | progress destruct_head'_ex
                            | progress subst
                            | progress inversion_sigma
                            | progress cbn [eq_rect type_of_rawexpr expr.interp expr_interp_related type_of_rawexpr] in *
                            | assumption
                            | exfalso; assumption
                            | apply conj
                            | break_innermost_match_hyps_step
                            | solve [ eauto ]
                            | apply reify_interp_related ].
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
        Proof using raw_pident_to_typed_invert_bind_args_type raw_pident_to_typed_invert_bind_args invert_bind_args_unknown_correct pident_unify_unknown_correct.
          subst K res.
          revert dependent re; induction t as [t|s IHs d IHd]; cbn [assemble_identifier_rewriters' value'_interp];
            intros; fold (@type.interp); cbv [value_or_expr_interp_ok].
          { cbn [value_interp_related].
            destruct Ht; cbn [eq_rect].
            epose eval_rewrite_rules_correct.
            Search
            pattern (eval_rewrite_rules do_again dt rew_rules).
            generalize dependent (type_of_rawexpr re).

            remember (type.base t) as t' eqn:?.

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
                                | [ |- rew [?P] ?H in ?v === ?ev ]
                                  => is_evar ev;
                                     refine (_ : rew [P] H in v === rew [type.interp base.interp] H in _)
                                end
                              | assumption
                              | progress cbv [eq_sym eq_rect]
                              | break_innermost_match_step
                              | reflexivity
                              | apply expr_of_rawexpr_interp_related
                              | apply reify_interp_related ]. }


            { admit. }
            { admit. }
            {

            repeat match goal with
            { instantiate (1:=rew [type.interp base.interp] Ht in _).
              instantiate (1:=ltac:(eassumption)).
              destruct Ht; cbn [eq_rect].
              admit. }
            { admit. }
            { destruct Ht; cbn [eq_sym eq_rect]; assumption. }
            { instantiate (1:=ltac:(eassumption)).
              cbv [rValueOrExpr2]; break_innermost_match; cbn [eq_rect rawexpr_interp_related]; assumption. }
            { rewrite <- (eq_sym_involutive Ht); generalize (eq_sym Ht); clear Ht; intro Ht.

            Focus 3.
            unfold rValueOrExpr2 at 2.
            cbn [type_of_rawexpr] in IHd.
            rewrite value_interp_ok_arrow.
            split.
            { intros x y Hx Hy Hxy.
              repeat apply conj.
              3:etransitivity; [ | symmetry; etransitivity; [ | ] ].
              1-2: apply value_interp_ok_of_value_or_expr_interp_ok; try exact _.
              1-4: lazymatch goal with
                   | [ |- context[assemble_identifier_rewriters' _ _ _ _ ?re ?K] ] => apply (IHd re eq_refl)
                   end; clear IHd.
              all: repeat first [ progress cbn [eq_rect rawexpr_interp rawexpr_interp_ok] in *
                                | apply conj
                                | apply rawexpr_interp_ok_rValueOrExpr2_reify
                                | assumption ].
              1-4: repeat first [ progress cbv [rawexpr_interp_ok]
              1-2: lazymatch goal with
                   | [ |- context[assemble_identifier_rewriters' _ _ _ _ ?re ?K] ] => apply (IHd re eq_refl)
                   end; cbn [eq_rect] in *.
              2:apply IHd.
            Lemma
            cbv [value_interp_ok value'_interp_related].
          Print Compile.value_interp_ok.
          Search Compile.value'_interp.
          Print Compile.value'_interp.
          Print Compile.value_interp_ok.
          Focus 2.
          { cbn [type.related]; cbv [respectful id]; cbn [type_of_rawexpr] in *.
            intros.
            match goal with
            | [ |- assemble_identifier_rewriters' _ _ _ _ ?re _ === _ ]
              => specialize (fun v ev He => IHd v ev He re eq_refl)
            end.
            cbn [type_of_rawexpr eq_rect rawexpr_ok] in *.
            eapply IHd; cbn [expr_of_rawexpr expr.interp rawexpr_equiv_value type.related] in *; cbv [respectful] in *.
            { instantiate (1:=ltac:(destruct d)); destruct d; eapply Hv; solve [ eauto ]. }
            { repeat apply conj;
                try solve [ repeat first [ (idtac + symmetry); assumption
                                         | etransitivity; (idtac + symmetry); eassumption
                                         | apply rawexpr_ok_rValueOrExpr2_reify ] ].
              apply rawexpr_ok_rValueOrExpr2_reify.

        Definition rawexpr_interp (r : rawexpr) : type.interp base.interp (type_of_rawexpr r)
          := match r with
             | rValue t v => value'_interp v
             | rExpr t e => expr.interp ident_interp e
             | rIdent _ _ _ _ alt => expr.interp ident_interp alt
             | rApp _ _ _ alt => expr.interp ident_interp alt
             end.

        Lemma rawexpr_interp_ok_rValueOrExpr2_reify {t v}
          : value_or_expr_interp_ok v
            -> rawexpr_interp_ok (@rValueOrExpr2 _ _ t v (reify v)).
        Proof using Type.
          cbv [rValueOrExpr2 value_or_expr_interp_ok]; break_innermost_match; exact id.
        Qed.


        Lemma interp_assemble_identifier_rewriters'
              (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t))
              (dt : decision_tree)
              (rew_rules : rewrite_rulesT)
              t re K
              (res := @assemble_identifier_rewriters' dt rew_rules do_again t re K)
              (Ht : type_of_rawexpr re = t)
              (HK : K = (fun P v => rew [P] Ht in v))(*
                      /\ rew pf in value_of_rawexpr re = ev })*)
              (Hdo_again : forall G t e1 e2,
                  (forall t v1 v2, List.In (existT _ t (v1, v2)) G -> value'_interp v1 == v2)
                  -> expr.wf G e1 e2
                  -> expr.interp ident_interp (UnderLets.interp ident_interp (do_again t e1)) == expr.interp ident_interp e2)
              (Hrew_rules : rewrite_rules_interp_goodT rew_rules)
              (Hr : rawexpr_interp_ok re)
          : value_or_expr_interp_ok res
            /\ value'_interp res == rew Ht in rawexpr_interp re.
        Proof using raw_pident_to_typed_invert_bind_args_type raw_pident_to_typed_invert_bind_args invert_bind_args_unknown_correct pident_unify_unknown_correct.
          subst K res.
          revert dependent re; induction t as [t|s IHs d IHd]; cbn [assemble_identifier_rewriters' value'_interp];
            intros; fold (@type.interp); cbv [value_or_expr_interp_ok].
          { cbv [value_or_expr_interp_ok]. admit. }
          { rewrite value_interp_ok_arrow.
            split.
            { intros x y Hx Hy Hxy.
              repeat apply conj.
              3:etransitivity; [ | symmetry; etransitivity; [ | ] ].
              1-2: apply value_interp_ok_of_value_or_expr_interp_ok; try exact _.
              1-4: lazymatch goal with
                   | [ |- context[assemble_identifier_rewriters' _ _ _ _ ?re ?K] ] => apply (IHd re eq_refl)
                   end; clear IHd.
              all: repeat first [ progress cbn [eq_rect rawexpr_interp rawexpr_interp_ok] in *
                                | apply conj
                                | apply rawexpr_interp_ok_rValueOrExpr2_reify
                                | assumption ].
              1-4: repeat first [ progress cbv [rawexpr_interp_ok]
              1-2: lazymatch goal with
                   | [ |- context[assemble_identifier_rewriters' _ _ _ _ ?re ?K] ] => apply (IHd re eq_refl)
                   end; cbn [eq_rect] in *.
              2:apply IHd.
            Lemma
            cbv [value_interp_ok value'_interp_related].
          Print Compile.value_interp_ok.
          Search Compile.value'_interp.
          Print Compile.value'_interp.
          Print Compile.value_interp_ok.
          Focus 2.
          { cbn [type.related]; cbv [respectful id]; cbn [type_of_rawexpr] in *.
            intros.
            match goal with
            | [ |- assemble_identifier_rewriters' _ _ _ _ ?re _ === _ ]
              => specialize (fun v ev He => IHd v ev He re eq_refl)
            end.
            cbn [type_of_rawexpr eq_rect rawexpr_ok] in *.
            eapply IHd; cbn [expr_of_rawexpr expr.interp rawexpr_equiv_value type.related] in *; cbv [respectful] in *.
            { instantiate (1:=ltac:(destruct d)); destruct d; eapply Hv; solve [ eauto ]. }
            { repeat apply conj;
                try solve [ repeat first [ (idtac + symmetry); assumption
                                         | etransitivity; (idtac + symmetry); eassumption
                                         | apply rawexpr_ok_rValueOrExpr2_reify ] ].
              apply rawexpr_ok_rValueOrExpr2_reify.

              Set Printing All.
              apply
            do 4 esplit; [ eassumption | eapply rawexpr_equiv_value_rValueOrExpr2_reify; reflexivity ]. }
          Unfocus.
          { set (t' := type.base t) in pf, He.
            revert v Hv.
            change (base.interp t) with (type.interp base.interp t').
            change (type.base t) with t'.
            assert (Ht : type.base t = t') by reflexivity.
            clearbody t'.
            destruct pf; cbn [eq_rect] in *; intros.
            eapply interp_eval_rewrite_rules; auto. }
          { cbn [type.related]; cbv [respectful id]; cbn [type_of_rawexpr] in *.
            intros.
            match goal with
            | [ |- assemble_identifier_rewriters' _ _ _ _ ?re _ === _ ]
              => specialize (fun e => IHd e re eq_refl)
            end.
            cbn [type_of_rawexpr eq_rect] in *.
            eapply IHd; cbn [expr_of_rawexpr expr.interp rawexpr_equiv_expr type.related] in *; cbv [respectful rValueOrExpr2] in *.
            all: repeat first [ apply interp_reify
                              | reflexivity
                              | progress cbn [rawexpr_equiv_expr]
                              | match goal with
                                | [ |- and _ _ ] => apply conj
                                | [ H : _ |- _ ] => apply H; clear H
                                end
                              | break_innermost_match_step ]. }
        Qed.







        (*Local Infix "===" := (@value_interp_related1 ident ident_interp _ _) : type_scope.*)
        Local Infix "====" := (@value'_interp_related ident ident_interp _ _ _) : type_scope.
        Local Notation "e1 ===== e2" := (existT expr _ e1 = existT expr _ e2) : type_scope.
        Local Notation "e1 ====== e2" := (existT (value' _) _ e1 = existT (value' _) _ e2) : type_scope.

        Local Notation maybe_to_expr with_lets
          := (if with_lets as wl return (if wl then _ else _) -> expr _
              then UnderLets.to_expr
              else (fun x => x)).

        TODO: canonical interpretation of value by reify -> interp
        Lemma interp_Base_value {t} v1 v2
          : v1 === v2 -> @Base_value t v1 === v2.
        Proof using Type.
          cbv [Base_value]; break_innermost_match; cbn [value_interp_related1 UnderLets.interp]; fold (@type.interp);
            exact id.
        Qed.

        Fixpoint interp_reify {with_lets t e v} {struct t}
          : e === v
            -> expr.interp ident_interp (@reify with_lets t e) == v
        with interp_reflect {with_lets t e v} {struct t}
          : expr.interp ident_interp e == v
            -> @reflect with_lets t e === v.
        Proof using Type.
          all: destruct t as [t|s d];
            [ clear interp_reify interp_reflect
            | pose proof (fun with_lets => interp_reify with_lets s) as interp_reify_s;
              pose proof (fun with_lets => interp_reify with_lets d) as interp_reify_d;
              pose proof (fun with_lets => interp_reflect with_lets s) as interp_reflect_s;
              pose proof (fun with_lets => interp_reflect with_lets d) as interp_reflect_d;
              clear interp_reify interp_reflect ].
          all: repeat first [ progress cbn [reflect reify type.related value_interp_related1 expr.interp] in *
                            | progress cbv [respectful]
                            | progress fold (@reify) (@reflect) in *
                            | break_innermost_match_step
                            | rewrite UnderLets.interp_to_expr
                            | exact id
                            | progress intros
                            | match goal with
                              | [ H : _ |- _ ] => apply H; clear H
                              end ].
        Qed.

        Lemma eqv_refl_of_value_interp_related1 {with_lets t v e1 e2}
          : @value_interp_related1 ident ident_interp with_lets t v e1
            -> @value_interp_related1 ident ident_interp with_lets t v e2
            -> e1 == e2.
        Proof using Type.
          revert with_lets v; induction t as [|s IHs d IHd]; cbn [value_interp_related1 type.related]; cbv [respectful]; [ intros; subst; reflexivity | ]; intros.
          eapply IHd; match goal with H : _ |- _ => apply H end.
          all: eapply @interp_reflect with (e:=expr.Var _); cbn [expr.interp].
          all: (idtac + (etransitivity; (idtac + symmetry))); eassumption.
        Qed.

        Global Instance value_interp_related1_Proper_iff {with_lets t v}
          : Proper (type.eqv ==> iff) (@value_interp_related1 ident ident_interp with_lets t v) | 10.
        Proof using Type.
          cbv [Proper respectful].
          revert with_lets v; induction t as [|s IHs d IHd]; cbn [value_interp_related1 type.related]; cbv [respectful].
          { intros; subst; reflexivity. }
          { split; intros; (eapply IHd; [ | now eauto ]).
            all: match goal with H : _ |- _ => (idtac + symmetry); apply H end.
            all: eapply eqv_refl_of_value_interp_related1; eassumption. }
        Qed.

        Global Instance value_interp_related1_Proper_impl {with_lets t v}
          : Proper (type.eqv ==> Basics.impl) (@value_interp_related1 ident ident_interp with_lets t v) | 10.
        Proof using Type.
          intros ? ? H; destruct (@value_interp_related1_Proper_iff with_lets t v _ _ H); assumption.
        Qed.

        Global Instance value_interp_related1_Proper_flip_impl {with_lets t v}
          : Proper (type.eqv ==> Basics.flip Basics.impl) (@value_interp_related1 ident ident_interp with_lets t v) | 10.
        Proof using Type.
          intros ? ? H; destruct (@value_interp_related1_Proper_iff with_lets t v _ _ H); assumption.
        Qed.

        Lemma rawexpr_equiv_value_rValueOrExpr2_reify {t v v'}
          : v = v'
            -> @rawexpr_equiv_value t v' (@rValueOrExpr2 _ _ t v (reify v)).
        Proof using Type.
          intro; subst; cbv [rawexpr_equiv_value rValueOrExpr2]; break_innermost_match; reflexivity.
        Qed.

        Fixpoint rawexpr_ok (r : rawexpr) : Prop
          := match r with
             | rValue t e => e ==== e
             | rExpr t e => expr.interp ident_interp e == expr.interp ident_interp e
             | rIdent _ t idc t' alt
               => expr.Ident idc ===== alt
             | rApp f x t alt
               => rawexpr_ok f
                  /\ rawexpr_ok x
                  /\ exists s d
                            (pff : type_of_rawexpr f = type.arrow s d)
                            (pfx : type_of_rawexpr x = s),
                      ((rew pff in expr_of_rawexpr f) @ (rew pfx in expr_of_rawexpr x))%expr
                        ===== alt
             end.

        Lemma rawexpr_ok_rValueOrExpr2_reify {t v}
          : v ==== v
            -> rawexpr_ok (@rValueOrExpr2 _ _ t v (reify v)).
        Proof using Type.
          intro; subst; cbv [rawexpr_ok rValueOrExpr2]; break_innermost_match; assumption.
        Qed.



        Lemma interp_assemble_identifier_rewriters
              (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t))
              (d : decision_tree)
              (rew_rules : rewrite_rulesT)
              t idc
              (res := @assemble_identifier_rewriters d rew_rules do_again t idc)
              (Hdo_again : forall G t e1 e2,
                  (forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 === v2)
                  -> expr.wf G e1 e2
                  -> expr.interp ident_interp (UnderLets.interp ident_interp (do_again t e1)) == expr.interp ident_interp e2)
              (Hrew_rules : rewrite_rules_interp_goodT rew_rules)
          : res === ident_interp t idc.
        Proof using eta_ident_cps_correct raw_pident_to_typed_invert_bind_args_type raw_pident_to_typed_invert_bind_args invert_bind_args_unknown_correct pident_unify_unknown_correct ident_interp_Proper.
          subst res; cbv [assemble_identifier_rewriters].
          rewrite eta_ident_cps_correct.
          apply interp_assemble_identifier_rewriters' with (e:=expr.Ident idc);
            cbn [type_of_rawexpr rawexpr_equiv_expr expr.interp]; cbv [id eq_rect]; try (exists eq_refl); try apply ident_interp_Proper; eauto.
        Qed.
      End with_interp.


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

        (*
        Lemma unify_pattern'_good_for_normalize {t evm} {re} {p : pattern t}
              {K : type -> Type}
              {P' : forall t, K t -> Prop}
              {k T k' v'}
              (P : T -> Prop)
              (retT := P' (pattern.type.subst_default t evm))
              (HretT : forall v v', retT v -> k' v = Some v' -> P v')
              (Hk : under_with_unification_resultT'_relation1 (P' _) k)
          : @unify_pattern' _ re p evm K k T k' = Some v'
            -> P v'.
        Proof using pident_unify_unknown_correct.
          subst retT; revert T P K P' evm k' k re v' HretT Hk.
          cbv [under_with_unification_resultT'_relation1 deep_rewrite_ruleTP_gen_ok_relation].
          induction p; cbn [unify_pattern' under_with_unification_resultT'_relation1_gen]; intros *.
          all: repeat first [ break_innermost_match_step
                            | progress cbv [option_bind']
                            | progress cbn [Option.bind eq_rect pattern.type.subst_default] in *
                            | progress inversion_option
                            | progress subst
                            | progress rewrite_type_transport_correct
                            | progress type_beq_to_eq
                            | congruence
                            | rewrite pident_unify_unknown_correct
                            | progress cbv [Option.bind] in *
                            | progress intros
                            | match goal with
                              | [ H : type_of_rawexpr ?re = _ |- _ ]
                                => generalize dependent (value_of_rawexpr re); generalize dependent (type_of_rawexpr re); try clear re; intros; progress subst
                              | [ H : unify_pattern' ?re ?p ?k ?K ?v = _ |- _ ]
                                => lazymatch v with
                                   | @Some _ => fail
                                   | _ => idtac
                                   end;
                                   rewrite unify_pattern'_cps_id in H
                              | [ H : under_type_of_list_relation1_cps _ _ |- _ ]
                                => rewrite related1_app_type_of_list_under_type_of_list_relation1_cps in H
                              end
                            | break_match_hyps_step ltac:(fun _ => idtac)
                            | solve [ eauto ] ].
          (* Special evar management for the [p1 @ p2] case *)
          repeat first [ match goal with
                         | [ H : context[unify_pattern' _ ?p _ _ _ = Some _ -> _],
                                 H' : unify_pattern' _ ?p _ _ _ = Some ?k0,
                                      H'' : ?k' ?k0 = Some ?v'
                             |- ?P ?v' ]
                           => is_var k';
                              eapply H; revgoals;
                              [ rewrite unify_pattern'_cps_id;
                                lazymatch goal with
                                | [ H : unify_pattern' ?re ?p ?k ?K _ = Some _ |- Option.bind (unify_pattern' ?re' ?p ?k' _ _) ?ret = Some _ ]
                                  => let ret' := fresh in
                                     set (ret' := ret); setoid_rewrite H; subst ret'
                                end; cbn [Option.bind]; eassumption
                              | | intros; eapply HretT; try eassumption; [] ];
                              cbv beta; clear H; revgoals
                         | [ H : context[unify_pattern' _ ?p _ _ _ = Some _ -> _],
                                 H' : unify_pattern' _ ?p _ _ _ = Some ?w
                             |- ?P ?w ]
                           => eapply H; revgoals;
                              [ rewrite unify_pattern'_cps_id;
                                lazymatch goal with
                                | [ H : unify_pattern' ?re ?p ?k ?K _ = Some _ |- Option.bind (unify_pattern' ?re' ?p ?k' _ _) ?ret = Some _ ]
                                  => let ret' := fresh in
                                     set (ret' := ret); setoid_rewrite H; subst ret'
                                end; cbn [Option.bind]; reflexivity
                              | | ]; cbv beta; clear H; revgoals
                         end
                       | progress intros
                       | progress subst
                       | progress inversion_option
                       | progress cbn [type.codomain] in *
                       | solve [ auto using under_with_unification_resultT'_relation1_gen_always ]
                       | match goal with
                         | [ H : ?P (type.arrow ?s ?d) ?v |- ?F _ ?x (?P' ?d) ?v ]
                           => lazymatch type of v with
                              | ?T (?K d)
                                => let __ := open_constr:(eq_refl : P = (fun sd (v : T (K (type.codomain sd))) => F _ x (P' (type.codomain sd)) v)) in
                                   cbn [type.codomain]; exact H
                              end
                         | [ H : ?P ?s ?v |- ?P' ?d ?v ]
                           => is_var P'; is_var v; is_evar P;
                              unify P (fun _ : type => P' d); exact H
                         end ].
        Qed.

        Lemma unify_pattern_good_for_normalize {should_do_again with_opt under_lets is_cps re v} {t p k}
              (retT := @normalize_deep_rewrite_rule_cps_id_hypsT ident var should_do_again with_opt under_lets is_cps (type_of_rawexpr re) v)
              (Hk
               : under_with_unification_resultT_relation1
                   (fun evm => deep_rewrite_ruleTP_gen_ok_relation)
                   k)
          : @unify_pattern t _ p _ k _ (@Some _) = Some v
            -> retT.
        Proof using pident_unify_unknown_correct.
          subst retT.
          cbv [unify_pattern].
          rewrite unify_types_cps_id.
          unfold Option.bind at 1 2.
          break_innermost_match; try congruence; [].
          cbv [under_with_unification_resultT_relation1] in Hk.
          rewrite pattern.type.app_forall_vars_under_forall_vars_relation1 in Hk.
          specialize (Hk _ _ ltac:(eassumption)).
          eapply unify_pattern'_good_for_normalize; [ | refine Hk ].
          intros *.
          rewrite_type_transport_correct; break_match; type_beq_to_eq; cbn [Option.bind] in *; try congruence; [].
          inversion_option; subst.
          generalize dependent (type_of_rawexpr re); intros; subst.
          cbn [eq_rect]; cbv [id].
          assumption.
        Qed.*)

        Lemma interp_maybe_do_again_gen
              (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t))
              (Hdo_again : forall G t e1 e2,
                  (forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 === v2)
                  -> expr.wf G e1 e2
                  -> expr.interp ident_interp (UnderLets.interp ident_interp (do_again t e1)) == expr.interp ident_interp e2)
              {should_do_again : bool} {t}
              {e1 e2}
              (retT := expr.interp ident_interp (UnderLets.interp ident_interp (@maybe_do_again ident var do_again should_do_again t e1))
                       == expr.interp ident_interp e2)
              (He
               : match should_do_again return @Compilers.expr _ _ (if should_do_again then value else var) (type.base t) -> Prop with
                 | true
                   => fun e1
                      => exists G,
                          (forall t v1 v2,
                              List.In (existT _ t (v1, v2)) G
                              -> v1 === v2)
                          /\ expr.wf G e1 e2
                 | false
                   => fun e1
                      => expr.interp ident_interp e1 == expr.interp ident_interp e2
                 end e1)
          : retT.
        Proof using Type.
          subst retT; cbv [maybe_do_again]; break_innermost_match; cbn [UnderLets.interp]; destruct_head'_ex; destruct_head'_and;
            [ eapply Hdo_again; eassumption | assumption ].
        Qed.

        Lemma interp_maybe_do_again
              (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t))
              (Hdo_again : forall G t e1 e2,
                  (forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 === v2)
                  -> expr.wf G e1 e2
                  -> expr.interp ident_interp (UnderLets.interp ident_interp (do_again t e1)) == expr.interp ident_interp e2)
              {should_do_again : bool} {t}
              {G e1 e2}
              (retT := expr.interp ident_interp (UnderLets.interp ident_interp (@maybe_do_again ident var do_again should_do_again t e1))
                       == expr.interp ident_interp e2)
              (Hwf : expr.wf G e1 e2)
              (HG
               : forall t v1 v2,
                  List.In (existT _ t (v1, v2)) G
                  -> (if should_do_again return (if should_do_again then value else var) t -> _
                      then fun v1 => v1 === v2
                      else fun v1 => v1 == v2)
                       v1)
          : retT.
        Proof using ident_interp_Proper.
          apply interp_maybe_do_again_gen; [ assumption | ].
          break_innermost_match; [ solve [ eauto ] | ].
          eapply expr.wf_interp_Proper_gen1; eassumption.
        Qed.

        (*Lemma app_under_with_unification_resultT_relation_hetero
              {t p K1 K2 HP P v1 v2 evm}
          : @under_with_unification_resultT_relation_hetero t p K1 K2 HP P v1 v2
            -> option_eq
                 (@under_with_unification_resultT'_relation_hetero t p _ _ _ HP (P _))
                 (pattern.type.app_forall_vars v1 evm)
                 (pattern.type.app_forall_vars v2 evm).
        Proof.
          cbv [under_with_unification_resultT_relation_hetero].
          intros H'.
          apply @pattern.type.app_forall_vars_under_forall_vars_relation with (evm:=evm) in H'.
          assumption.
        Qed.
         *)
        (*
        Lemma interp_unify_pattern'_under_with_unification_resultT'_relation_hetero
              {t p evm re K1 K2 HP P v1 v2}
          : @under_with_unification_resultT'_relation_hetero t p evm (K1 _) (K2 _) HP P v1 v2
            -> option_eq
                 P
                 (@unify_pattern' t re p evm K1 v1 _ (@Some _))
                 (@unify_pattern' t re p evm K2 v2 _ (@Some _)).
        Proof using Type.
          revert re K1 K2 P v1 v2; induction p; intros;
            cbn [unify_pattern' under_with_unification_resultT'_relation_hetero with_unification_resultT'] in *.
          all: repeat first [ progress rewrite_type_transport_correct
                            | break_innermost_match_step
                            | progress type_beq_to_eq
                            | progress cbn [Option.bind option_eq eq_rect pattern.type.subst_default] in *
                            | progress cbv [option_bind' eq_rect] in *
                            | progress cbv [Option.bind]
                            | assumption
                            | reflexivity
                            | progress inversion_option
                            | progress intros
                            | apply related_app_type_of_list_of_under_type_of_list_relation_cps
                            | exfalso; assumption
                            | match goal with
                              | [ |- context[@unify_pattern' ?t ?re ?p ?evm ?K ?v ?T ?k] ]
                                => lazymatch k with
                                   | @Some _ => fail
                                   | _ => rewrite (@unify_pattern'_cps_id _ _ _ _ _ _ t re p evm K v T k)
                                   end
                              | [ H : @unify_pattern' ?t ?re ?p ?evm ?K1 ?v1 _ (@Some _) = _,
                                      H' : @unify_pattern' ?t ?re ?p ?evm ?K2 ?v2 _ (@Some _) = _,
                                           H'' : under_with_unification_resultT'_relation_hetero _ _ ?v1 ?v2,
                                                 IH : forall re' K1' K2' (P : K1' ?t' -> K2' ?t' -> Prop) v1' v2', under_with_unification_resultT'_relation_hetero _ _ _ _ -> _ |- _ ]
                                => specialize (IH re K1 K2 _ v1 v2 H''); cbv [option_eq] in IH; rewrite H, H' in IH
                              | [ H : under_with_unification_resultT'_relation_hetero _ _ ?v1 ?v2,
                                      IH : (forall re' K1' K2' (P : K1' ?t' -> K2' ?t' -> Prop) v1' v2', under_with_unification_resultT'_relation_hetero _ _ _ _ -> _)
                                  |- option_eq ?P'
                                               (@unify_pattern' ?t ?re ?p ?evm ?K1 ?v1 _ (@Some _))
                                               (@unify_pattern' ?t ?re ?p ?evm ?K2 ?v2 _ (@Some _)) ]
                                => refine (IH re K1 K2 _ v1 v2 H)
                              | [ H : _ |- _ ] => apply H; clear H
                              end ].
          1: exact admit.
        Qed.
*)
(*
        Lemma unify_pattern'_default_interp'_cps_id t p
          : forall KT re evm K,
            @unify_pattern' t re p _ KT (@pattern_default_interp' _ t p evm K) _ (@Some _)
            = option_map
                K
                (@unify_pattern' t re p _ _ (@pattern_default_interp' _ t p evm id) _ (@Some _)).
        Proof using Type.
          induction p; cbn [unify_pattern' pattern_default_interp'].
          all: repeat first [ progress intros
                            | progress rewrite_type_transport_correct
                            | break_innermost_match_step
                            | progress type_beq_to_eq
                            | progress inversion_option
                            | progress subst
                            | reflexivity
                            | progress cbn [Option.bind option_map pattern.type.subst_default type.codomain] in *
                            | progress cbv [option_bind'] in *
                            | progress cbv [Option.bind]
                            | progress break_match
                            | rewrite !app_lam_type_of_list
                            | match goal with
                              | [ |- context[@unify_pattern' ?t ?re ?p ?evm ?K ?x ?T ?v] ]
                                => lazymatch v with
                                   | @Some _ => fail
                                   | _ => idtac
                                   end;
                                   rewrite (@unify_pattern'_cps_id _ _ _ _ _ _ t re p evm K x T v)
                              | [ H : match ?x with _ => _ end = _ |- _ ] => destruct x eqn:?
                              | [ IH : (forall KT' re' evm' K', unify_pattern' _ ?p _ _ (@Some _) = _)
                                  |- context[@unify_pattern' ?t ?re ?p ?evm ?KT (pattern_default_interp' _ _ ?K) _ (@Some _)] ]
                                => lazymatch K with
                                   | (fun x => x) => fail
                                   | _ => idtac
                                   end;
                                   let IH' := fresh in
                                   pose proof (IH KT re evm K) as IH'; cbn [type.codomain] in *;
                                   rewrite IH'; clear IH'
                              | [ IH : (forall KT' re' evm' K', unify_pattern' _ ?p _ _ (@Some _) = _),
                                       H : context[@unify_pattern' ?t ?re ?p ?evm ?KT (pattern_default_interp' _ _ ?K) _ (@Some _)] |- _ ]
                                => lazymatch K with
                                   | (fun x => x) => fail
                                   | _ => idtac
                                   end;
                                   let IH' := fresh in
                                   pose proof (IH KT re evm K) as IH'; cbn [type.codomain] in *;
                                   rewrite IH' in H; clear IH'; cbv [option_map] in H
                              end
                            | progress cbv [option_map] ].
        Qed.
*)
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

        Lemma types_match_with_rawexpr_equiv_expr {t e re evm t' p}
          : @types_match_with evm t' re p
            -> @rawexpr_equiv_expr t e re
            -> t = pattern.type.subst_default t' evm.
        Proof using Type.
          revert t re e evm.
          induction p; cbn [types_match_with]; intros.
          all: repeat first [ congruence
                            | break_innermost_match_hyps_step
                            | exfalso; assumption
                            | progress destruct_head'_and
                            | progress subst
                            | progress inversion_sigma
                            | progress cbn [pattern.type.subst_default rawexpr_equiv_expr eq_rect] in *
                            | erewrite pattern.type.subst_Some_subst_default by eassumption
                            | match goal with
                              | [ H : forall t re e evm, types_match_with _ _ ?p -> _, H' : types_match_with _ _ ?p |- _ ]
                                => specialize (fun t e => H t _ e _ H')
                              | [ H : forall t e, rawexpr_equiv_expr e ?re -> _, H' : rawexpr_equiv_expr _ ?re |- _ ]
                                => specialize (H _ _ H')
                              | [ H : rawexpr_equiv_expr _ _ |- _ ]
                                => unique pose proof (rawexpr_equiv_expr_to_type_of_rawexpr H)
                              end ].
        Qed.

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
(*
        Lemma interp_unify_pattern'_default_interp' t p
          : forall re evm e e' v
                   (Hevm : types_match_with evm re p)
                   (Hre : @rawexpr_equiv_expr _ e' re),
            expr.interp ident_interp e' == v
            -> @unify_pattern' t re p _ _ (@pattern_default_interp' _ t p evm id) _ (@Some _) = Some e
            -> expr.interp ident_interp e == v.
        Proof using pident_unify_unknown_correct pident_unify_to_typed.
          induction p; cbn [unify_pattern' type.related pattern_default_interp' unify_types preunify_types pattern.type.unify_extracted].
          all: repeat first [ progress cbv [respectful option_bind' id] in *
                            | progress cbn [Option.bind rawexpr_equiv_expr eq_rect pattern.type.subst_default type.codomain expr.interp type.related preunify_types types_match_with] in *
                            | progress inversion_option
                            | progress inversion_sigma
                            | progress inversion_prod
                            | progress subst
                            | progress intros
                            | reflexivity
                            | assumption
                            | progress rewrite_type_transport_correct
                            | break_innermost_match_hyps_step
                            | progress destruct_head'_and
                            | progress type_beq_to_eq
                            | rewrite !app_lam_type_of_list
                            | rewrite pident_unify_unknown_correct in *
                            | exfalso; assumption
                            | match goal with
                              | [ H : unify_pattern' ?re ?p ?k ?K ?v = _ |- _ ]
                                => lazymatch v with
                                   | @Some _ => fail
                                   | _ => idtac
                                   end;
                                   rewrite unify_pattern'_cps_id in H
                              | [ H : match ?x with _ => _ end = Some _ |- _ ] => destruct x eqn:?
                              end
                            | progress cbv [Option.bind] in *
                            | progress expr.invert_match
                            | progress fold (@pattern.type.subst_default) in *
                            | match goal with
                              | [ H : types_match_with _ ?re ?p, H' : rawexpr_equiv_expr ?e ?re |- _ ]
                                => pose proof (types_match_with_rawexpr_equiv_expr H H'); progress subst
                              | [ H : context[@unify_pattern' ?t ?re ?p ?evm ?KT (pattern_default_interp' _ _ ?K) _ (@Some _)] |- _ ]
                                => lazymatch K with
                                   | (fun x => x) => fail
                                   | _ => idtac
                                   end;
                                   setoid_rewrite (@unify_pattern'_default_interp'_cps_id t p KT re evm K) in H; cbv [option_map] in H
                              | [ H : @unify_pattern' ?t ?re ?p ?evm ?KT (pattern_default_interp' _ _ ?K) _ (@Some _) = Some ?res,
                                      H' : types_match_with _ _ ?p,
                                           IH : forall re' evm' res' e' v', _ -> _ -> _ -> unify_pattern' _ ?p _ _ (@Some _) = _ -> _ |- _ ]
                                => specialize (fun e' v' H1 H2 => IH re evm res e' v' H' H1 H2 H); clear H H' p
                              end
                            | progress cbv [eq_rect]
                            | break_match_when_head_step (@eq)
                            | apply interp_reify
                            | unshelve erewrite pident_unify_to_typed' by eassumption
                            | progress eliminate_hprop_eq
                            | progress cbv [unify_types] in * ].
          Focus 2.
          etransitivity.
          eapply IHp1; [ eassumption | | eapply IHp2; [ eassumption | ] ].
          3: eassumption.
          Unfocus.
          1-3: exact admit.
        Qed.*)


        (*
        Lemma interp_unify_pattern'_default_interp' t p
          : forall KT re evm res K P
                   (*(Hre : @rawexpr_equiv_expr _ e' re)*),
            (*expr.interp ident_interp (K e') == v
            ->*) @unify_pattern' t re p _ KT (@pattern_default_interp' _ t p evm K) _ (@Some _) = Some res
                 -> (forall e, rawexpr_equiv_expr e re -> P (K e))
                 -> P res.
        Proof using Type.
          induction p; cbn [unify_pattern' type.related pattern_default_interp'].
          all: repeat first [ progress cbv [respectful option_bind'] in *
                            | progress cbn [Option.bind rawexpr_equiv_expr eq_rect pattern.type.subst_default type.codomain expr.interp type.related] in *
                            | progress inversion_option
                            | progress inversion_sigma
                            | progress subst
                            | progress intros
                            | progress rewrite_type_transport_correct
                            | break_innermost_match_hyps_step
                            | progress destruct_head'_and
                            | progress type_beq_to_eq
                            | exfalso; assumption
                            | match goal with
                              | [ H : unify_pattern' ?re ?p ?k ?K ?v = _ |- _ ]
                                => lazymatch v with
                                   | @Some _ => fail
                                   | _ => idtac
                                   end;
                                   rewrite unify_pattern'_cps_id in H
                              | [ H : match ?x with _ => _ end = Some _ |- _ ] => destruct x eqn:?
                              end
                            | progress cbv [Option.bind] in *
                            | progress expr.invert_match
                            | match goal with
                              | [ H : @unify_pattern' ?t ?re ?p ?evm ?KT (pattern_default_interp' _ _ ?K) _ (@Some _) = Some ?res,
                                      IH : forall KT' re' evm' res' K' P', unify_pattern' _ ?p _ _ (@Some _) = _ -> _ |- _ ]
                                => specialize (fun P' => IH KT re evm res K P' H); cbv beta in *; move IH at bottom
                              end ].
          Focus 4.
          { lazymatch goal with
            | [ H : @unify_pattern' ?t ?re ?p ?evm ?KT (pattern_default_interp' _ _ ?K) _ (@Some _) = Some ?res,
                    IH : forall KT' re' evm' res' K' P', unify_pattern' _ ?p _ _ (@Some _) = _ -> _ |- _ ]
              => specialize (fun P' => IH KT re evm res K P' H); cbv beta in *; move IH at bottom
            end.
          { specialize (
            eapply IHp2.
            refine H.


        Lemma interp_unify_pattern'_default_interp' t p
          : forall KT re evm e e' v K
                   (Hre : @rawexpr_equiv_expr _ e' re),
            expr.interp ident_interp (K e') == v
            -> @unify_pattern' t re p _ (fun t => expr (KT t)) (@pattern_default_interp' _ t p evm K) _ (@Some _) = Some e
            -> expr.interp ident_interp e == v.
        Proof using Type.

          induction p; cbn [unify_pattern' type.related pattern_default_interp'].
          (*all: intros; break_match_hyps.*)
          all: repeat first [ progress cbv [respectful option_bind'] in *
                            | progress cbn [Option.bind rawexpr_equiv_expr eq_rect pattern.type.subst_default type.codomain expr.interp type.related] in *
                            | progress inversion_option
                            | progress inversion_sigma
                            | progress subst
                            | progress intros
                            | progress rewrite_type_transport_correct
                            | break_innermost_match_hyps_step
                            | progress destruct_head'_and
                            | progress type_beq_to_eq
                            | exfalso; assumption
                            | match goal with
                              | [ H : unify_pattern' ?re ?p ?k ?K ?v = _ |- _ ]
                                => lazymatch v with
                                   | @Some _ => fail
                                   | _ => idtac
                                   end;
                                   rewrite unify_pattern'_cps_id in H
                              | [ H : match ?x with _ => _ end = Some _ |- _ ] => destruct x eqn:?
                              end
                            | progress cbv [Option.bind] in *
                            | progress expr.invert_match ].
          Focus 5.
          Check @unify_pattern'.
          match goal with
          | [ H : @unify_pattern' ?t ?re ?p ?evm ?KT (pattern_default_interp' _ _ ?K) _ (@Some _) = _,
                  IH : forall KT' re' evm' e e' v K', _ -> _ -> unify_pattern' _ ?p _ _ (@Some _) = _ -> _ |- _ ]
            => idtac KT
          end.
          {
          repeat first [ progress cbv [respectful option_bind'] in *
                                        | progress cbn [Option.bind rawexpr_equiv_expr eq_rect pattern.type.subst_default type.codomain expr.interp type.related] in *
                                        | progress inversion_option
                                        | progress inversion_sigma
                                        | progress subst
                                        | progress intros
                                        | progress rewrite_type_transport_correct
                                        | break_innermost_match_hyps_step
                                        | progress destruct_head'_and
                                        | progress type_beq_to_eq
                                        | exfalso; assumption
                                        | match goal with
                                          | [ H : unify_pattern' ?re ?p ?k ?K ?v = _ |- _ ]
                                            => lazymatch v with
                                               | @Some _ => fail
                                               | _ => idtac
                                               end;
                                               rewrite unify_pattern'_cps_id in H
                                          | [ H : match ?x with _ => _ end = Some _ |- _ ] => destruct x eqn:?
                                          end
                                        | progress cbv [Option.bind] in *
                                        | progress expr.invert_match ].
          Focus 2.
          move Heqo at bottom.
          Check @unify_pattern'.
          Check @pattern_default_interp'.
          Search Compile.pattern_default_interp'.
          Set Printing All.

         *)

        Lemma types_match_with_relax_evm t re p evm evm'
              (Hevm' : forall i v, PositiveMap.find i evm = v -> PositiveMap.find i evm' = v)
              (Hty : @types_match_with evm t re p)
          : @types_match_with evm' t re p.
        Proof using Type.
          revert re Hty; induction p; cbn [types_match_with]; intros.
          all: repeat first [ break_innermost_match_step
                            | exfalso; assumption
                            | progress destruct_head'_and
                            | apply conj
                            | solve [ eauto using pattern.type.subst_relax_evm ] ].
        Qed.
(*
        Lemma types_match_with_pattern_collect_vars t re p evm
              (evm' := (fold_right
                          (fun i k evm'
                           => k match PositiveMap.find i evm with
                                | Some v => PositiveMap.add i v evm'
                                | None => evm'
                                end) (fun evm => evm)
                          (List.rev (PositiveSet.elements (pattern_collect_vars p)))
                          (PositiveMap.empty _)))
              (Hty : @types_match_with evm t re p)
          : @types_match_with evm' t re p.
        Proof using Type.
          subst evm'.
          revert evm re Hty.
          induction p; cbn [types_match_with pattern.collect_vars pattern.type.collect_vars].
          eapply types_match_with_relax_evm; [ | eassumption ].
 *)
        (*
        Lemma interp_unify_pattern'_default_interp t re p evm r e e' v
              (evm' := (fold_right
                          (fun i k evm'
                           => k match PositiveMap.find i evm with
                                | Some v => PositiveMap.add i v evm'
                                | None => evm'
                                end) (fun evm => evm)
                          (List.rev (PositiveSet.elements (pattern_collect_vars p)))
                          (PositiveMap.empty _)))
              (Hty : types_match_with evm' re p)
              (Hre : @rawexpr_equiv_expr _ e' re)
          : expr.interp ident_interp e' == v
            -> pattern.type.app_forall_vars (@pattern_default_interp _ p) evm = Some r
            -> @unify_pattern' t re p _ _ r _ (@Some _) = Some e
            -> expr.interp ident_interp e == v.
        Proof using pident_unify_unknown_correct pident_unify_to_typed.
          subst evm'.
          intros H H'.
          revert r H' e e' v Hty Hre H.
          cbv beta iota.
          set (fr := fold_right _ _ _ _).
          revert evm fr.
          lazymatch goal with
          | [ |- forall evm, let fr := @?frv evm in forall r : @?k1 fr, @?R evm = Some r -> @?F fr r ]
            => refine (proj1 (@pattern.type.app_forall_vars_under_forall_vars_relation1 _ k1 F _) _)
          end.
          cbv [pattern_default_interp].
          rewrite pattern.type.under_forall_vars_relation1_lam_forall_vars; intros ls' Hls' evm.
          clearbody evm; clear ls' Hls'.
          revert re.
          intros; eapply interp_unify_pattern'_default_interp'; try eassumption.
        Qed.
*)


        (*Lemma interp_unify_pattern'_default_interp t re p e e' v
              (Hre : @rawexpr_equiv_expr _ e re)
          : expr.interp ident_interp e == v
            -> unify_pattern re p (@pattern_default_interp t p) _ (@Some _) = Some e'
            -> expr.interp ident_interp e' == v.
        Proof using Type.
          (*revert re e' e v Hre.
          induction p; intros re e' e v Hre He Hu.
          Focus 2.

          { repeat first [ progress cbv [pattern_default_interp unify_pattern] in *
                         | rewrite unify_types_cps_id; unfold Option.bind at 1; break_innermost_match_step; [ | congruence ] ].
            cbv [unify_types preunify_types] in *.

            repeat first [
                         | rewrite unify_types_cps_id ].
            rewrite *)
          cbv [pattern_default_interp unify_pattern].
          rewrite unify_types_cps_id; unfold Option.bind at 1; break_innermost_match_step; [ | congruence ].
          unfold Option.bind at 1; break_innermost_match_step; [ | congruence ].
          rewrite unify_pattern'_cps_id; unfold Option.bind at 1; break_match; [ | congruence ].
          rewrite_type_transport_correct; break_match; type_beq_to_eq; cbn [Option.bind] in *; inversion_option; subst; [ | congruence ].
          cbv [id eq_rect] in *.
          break_match_when_head_step (@eq).

        Admitted.
*)
        (*Lemma interp_unify_pattern_default_interp t re p e e' v
              (Hre : @rawexpr_equiv_expr _ e re)
          : expr.interp ident_interp e == v
            -> unify_pattern re p (@pattern_default_interp t p) _ (@Some _) = Some e'
            -> expr.interp ident_interp e' == v.
        Proof using Type.
          (*revert re e' e v Hre.
          induction p; intros re e' e v Hre He Hu.
          Focus 2.

          { repeat first [ progress cbv [pattern_default_interp unify_pattern] in *
                         | rewrite unify_types_cps_id; unfold Option.bind at 1; break_innermost_match_step; [ | congruence ] ].
            cbv [unify_types preunify_types] in *.

            repeat first [
                         | rewrite unify_types_cps_id ].
            rewrite *)
          cbv [pattern_default_interp unify_pattern].
          rewrite unify_types_cps_id; unfold Option.bind at 1; break_innermost_match_step; [ | congruence ].
          unfold Option.bind at 1; break_innermost_match_step; [ | congruence ].
          rewrite unify_pattern'_cps_id; unfold Option.bind at 1; break_match; [ | congruence ].
          rewrite_type_transport_correct; break_match; type_beq_to_eq; cbn [Option.bind] in *; inversion_option; subst; [ | congruence ].
        Admitted.*)

        (*
/---- e1 ~ e2
|     \
|     R1 ~ R2
|     V
|     d1 ~ d2  (and also elementwise interp related)
|     V |
\---  a1|
|       V
\------ E1 ~ E2

Lemma 2: wf_data_related -> interp_data_related
Lemma 3: wf e1 e2 -> structural e1 r1 -> wf e1' r1 e2' r2 -> wf e1 a1 (or wf a1 e2?)
good rewrite rule : interp_data_related d1 d2 -> interp_related a1 (rewrite on d2)
Lemma 4: glue together
         *)

        Lemma value_interp_related1_value_of_rawexpr_of_rawexpr_equiv_expr
              {G} {re e}
              (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 == v2)
          : @rawexpr_equiv_expr _ e re
            -> expr.wf G e e
            -> value_of_rawexpr re === expr.interp ident_interp e.
        Proof using Type.
          revert e; induction re; cbn.
          all: repeat first [ reflexivity
                            | exfalso; assumption
                            | assumption
                            | progress intros
                            | progress subst
                            | progress destruct_head'_and
                            | progress inversion_sigma
                            | progress destruct_head'_sig
                            | progress cbn [eq_rect expr.interp] in *
                            | progress eliminate_hprop_eq
                            | progress expr.inversion_wf_constr
                            | match goal with
                              | [ |- reflect _ === _ ] => apply interp_reflect
                              | [ |- ident_interp _ _ == ident_interp _ _ ] => apply ident_interp_Proper
                              | [ H : expr.wf _ ?e ?e |- expr.interp _ ?e == expr.interp _ ?e ]
                                => eapply expr.wf_interp_Proper_gen1; [ | exact H ]
                              end
                            | break_innermost_match_hyps_step ].


          erewrite interp_reify.
          apply
          Lemma valu
          Search value_interp_related1.
          Print value_interp_related1.
          Focus 2.
          lazymatch goal with
          end.
          Search reflect value_interp_related1.
          Print Compile.rawexpr_equiv_expr.
          revert

        Lemma app_transport_pattern_default_interp'_cps_id
              {t p evm1 evm2 K f x}
          : @app_transport_with_unification_resultT'_cps
              t p evm1 evm2 _
              (@pattern_default_interp' K t p _ f)
              x _ (@Some _)
            = option_map
                f
                (@app_transport_with_unification_resultT'_cps
                   t p evm1 evm2 _
                   (@pattern_default_interp' _ t p _ id)
                   x _ (@Some _)).
        Proof using Type.
          cbv [id]; revert evm1 evm2 K f x; induction p; cbn; intros.
          all: repeat first [ reflexivity
                            | progress cps_id'_with_option app_transport_with_unification_resultT'_cps_id
                            | progress rewrite_type_transport_correct
                            | break_innermost_match_step
                            | progress type_beq_to_eq
                            | progress cbn [Option.bind option_map] in *
                            | rewrite !app_lam_type_of_list
                            | progress fold (@with_unification_resultT') in *
                            | match goal with
                              | [ IH : forall a b c d e, _ = option_map _ _ |- _ ]
                                => etransitivity; rewrite IH; clear IH; [ reflexivity | ]
                              end
                            | progress cbv [option_map] ].
        Qed.

        Lemma interp_rewrite_with_default_rule_helper
              {t'} {p : pattern t'} {evm evm'} {G}
              (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 == v2)
          : forall {d e re e2}
                   (Hevm : types_match_with evm re p)
                   (Hevm' : types_match_with evm' re p)
                   (Hup : unify_pattern' re p evm' _ (@Some _) = Some d)
                   (Happ : app_transport_with_unification_resultT'_cps (pattern_default_interp' p evm id) d _ (@Some _) = Some e2)
                   (Hre : @rawexpr_equiv_expr _ e re)
                   (e_ok : expr.wf G e e),
            expr.interp ident_interp e2 == expr.interp ident_interp e.
        Proof using Type.
          induction p; cbn [unify_pattern' app_transport_with_unification_resultT'_cps types_match_with]; intros.
          all: repeat first [ progress cbn [Option.bind pattern_default_interp' expr.interp eq_rect rawexpr_equiv_expr] in *
                            | progress cbv [option_bind'] in *
                            | assumption
                            | exfalso; assumption
                            | progress fold (@with_unification_resultT') in *
                            | match goal with
                              | [ H : context[app_transport_with_unification_resultT'_cps (pattern_default_interp' _ _ ?fv) _ _ ?k] |- _ ]
                                => lazymatch fv with
                                   | (fun x => x) => fail
                                   | @id _ => fail
                                   | _ => idtac
                                   end;
                                   lazymatch k with
                                   | @Some _ => idtac
                                   | (fun x => Some x) => idtac
                                   end;
                                   rewrite @app_transport_pattern_default_interp'_cps_id with (f:=fv) in H;
                                   cbv [option_map] in H
                              | [ H : @rawexpr_equiv_expr (type.arrow ?s (pattern.type.subst_default ?d ?evm)) ?e ?re,
                                      H' : types_match_with ?evm ?re ?p |- _ ]
                                => let H'' := fresh in
                                   is_var s; pose proof (types_match_with_rawexpr_equiv_expr H' H) as H'';
                                   cbn [pattern.type.subst_default] in H''; type.inversion_type
                              | [ H : forall d0 e re e2, types_match_with ?evm re ?p -> _,
                                    H' : types_match_with ?evm _ ?p |- _ ]
                                => specialize (fun d0 e e2 => H d0 e _ e2 H')
                              | [ H : forall d0 e e2, types_match_with ?evm ?re ?p -> _,
                                    H' : types_match_with ?evm ?re ?p |- _ ]
                                => specialize (fun d0 e e2 => H d0 e e2 H')
                              | [ H : forall d0 e e2, Some ?v = Some d0 -> _ |- _ ]
                                => specialize (fun e e2 => H v e e2 eq_refl)
                              | [ H : forall e e2, app_transport_with_unification_resultT'_cps (pattern_default_interp' ?p _ (fun x => x)) _ _ (@Some _) = Some e2 -> _,
                                    H' : app_transport_with_unification_resultT'_cps (pattern_default_interp' ?p _ (fun x => x)) _ _ _ = Some _ |- _ ]
                                => specialize (fun e => H e _ H')
                              | [ H : forall e0, rawexpr_equiv_expr e0 ?re -> _,
                                    H' : rawexpr_equiv_expr _ ?re |- _ ]
                                => specialize (H _ H')
                              end
                            | progress cbn [fst snd] in *
                            | progress expr.invert_match
                            | progress subst
                            | progress destruct_head'_and
                            | progress inversion_option
                            | progress inversion_sigma
                            | progress destruct_head'_sig
                            | progress rewrite_type_transport_correct
                            | progress type_beq_to_eq
                            | progress specialize_by_assumption
                            | progress cps_id'_with_option unify_pattern'_cps_id
                            | progress cps_id'_with_option app_transport_with_unification_resultT'_cps_id
                            | progress expr.inversion_wf_constr
                            | progress eliminate_hprop_eq
                            | rewrite pident_unify_unknown_correct in *
                            | break_match_step ltac:(fun v => match v with Sumbool.sumbool_of_bool _ => idtac end)
                            | break_match_hyps_step ltac:(fun v => match v with Sumbool.sumbool_of_bool _ => idtac end)
                            | break_innermost_match_step
                            | break_innermost_match_hyps_step
                            | rewrite !app_lam_type_of_list
                            | match goal with
                              | [ |- expr.interp _ (reify _) == _ ]
                                => apply interp_reify
                              | [ |- context[rew ?pf in _] ] => is_var pf; destruct pf
                              | [ |- context[pident_to_typed _ _ _ _] ]
                                => erewrite pident_unify_to_typed' with (pf:=eq_refl) by eassumption
                              | [ H : match ?x with Some _ => _ | None => None end = _ |- _ ]
                                => destruct x eqn:?
                              | [ H : match rew ?pf in expr.Abs _ with expr.Abs _ _ _ => False | _ => _ end |- _ ]
                                => exfalso; clear -H; destruct pf; cbn [eq_rect] in *
                              | [ |- ident_interp _ _ == ident_interp _ _ ] => apply ident_interp_Proper; reflexivity
                              | [ H : _ == _ |- _ == _ ] => apply H; assumption
                              end
                            | progress cbv [Option.bind] in * ].
          Focus 2.
          match goal with
          hyp_appl
          cbn [type.related] in *.
          match goal with
          end.

          expr.wf_inv
          wf_in
          rewrite
          lazymatch goal with
          | [ H : forall ev, ?e == ev -> _, H' : ?e == _ |- _ ] => specialize (H _ H')
          end.
          lazymatch goal with
          end.
                H'' : types_match_with _ ?re ?p |- _ ]
            => pose proof (types_match_with_rawexpr_equiv_expr H'' H')
          end.
          end.

          lazymatch goal with
          | [ H : match ?t with type.base _ => False | type.arrow s d => @?P s d end |- _ ]
            => match goal with
               | [ H' : context[rew ?F H in _] |- _ ]
                 => generalize dependent (F H); clear H; intro H
               end
          end.
          rewrite <- (eq_sym_involutive pf).
          case (eq_sym pf).

          Search eq_sym.
            => let H' := fresh in
               transparent assert (H' : { s : _ & { d : _ | type.arrow s d = t /\ P s d } })
                 by (clear -H; destruct t; [ exfalso; assumption | eauto ])
          end.
          assert (
          assert

          clear -
          match goal with
          | [ H : context[pattern.type.subst_default (type.arrow ?s ?d) _], H' : context[pattern.type.subst_default ?d ?evm] |- _ ]
            => change (pattern.type.subst_default d evm) with (type.codomain (pattern.type.subst_default (type.arrow s d) evm)) in *
          end.
          move d at bottom.
          generalize dependent (pattern.type.subst_default d evm).
          match goal with
              end.
          lazymatch goal with
          end.

          match goal with
          end.
          match goal with
          end.
          move e2 at bottom.
          match goal with
          end.
          Print with_unification_resultT'.

          move d at bottom.

          remember (pattern.type.subst_default d evm) eqn:? in *.
          destruct (pattern.type.subst_default d evm) eqn:?.

          expr.invert_subst.
          expr.inversion_expr.
          match goal with
          end.

          .

          apply Sigma.path_sigT_uncurried.
          Search eq sigT.
          Set Printing All.
          erewrite interp_reify.
          2:reflexivity.
          Search ident_interp pident_to_typed.
          Search app_type_of_list lam_type_of_list.
          all: cbn [pattern_default_interp'].
          *)

        Lemma interp_rewrite_with_default_rule
              (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t))
              {ap}
              (rewr : rewrite_ruleT := existT rewrite_ruleTP ap {| rew_replacement := pattern_default_interp (pattern.pattern_of_anypattern ap) |})
              t e re v ev
          : rewrite_with_rule do_again e re rewr = Some v
            -> @rawexpr_equiv_expr t e re
            -> expr.interp ident_interp e == ev
            -> expr.interp ident_interp (UnderLets.interp ident_interp v) == ev.
        Proof using pident_unify_to_typed.
          destruct ap as [t' p]; subst rewr; cbv [rewrite_with_rule rew_should_do_again pattern.type_of_anypattern pattern.pattern_of_anypattern rew_under_lets rew_with_opt rew_replacement normalize_deep_rewrite_rule maybe_do_again app_with_unification_resultT_cps option_bind' pattern_default_interp unify_pattern] in *; cbn [projT1 projT2] in *.
          repeat first [ match goal with
                         | [ |- Option.bind ?x _ = Some _ -> _ ]
                           => destruct x eqn:?; cbn [Option.bind]; [ | intros; solve [ inversion_option ] ]
                         end
                       | progress cps_id'_with_option unify_pattern_cps_id
                       | progress cps_id'_with_option unify_types_cps_id
                       | progress cps_id'_with_option unify_pattern'_cps_id
                       | progress cps_id'_with_option app_transport_with_unification_resultT'_cps_id
                       | progress cps_id'_with_option app_with_unification_resultT_cps_id ].
          repeat first [ break_match_step ltac:(fun v => match v with Sumbool.sumbool_of_bool _ => idtac end)
                       | progress rewrite_type_transport_correct
                       | progress type_beq_to_eq
                       | progress cbv [option_bind'] in *
                       | progress cbn [Option.bind projT1 projT2 UnderLets.interp eq_rect] in *
                       | progress destruct_head'_sigT
                       | progress destruct_head'_sig
                       | progress inversion_option
                       | progress subst
                       | solve [ intros; inversion_option ]
                       | rewrite !UnderLets.interp_splice
                       | match goal with
                         | [ H : pattern.type.app_forall_vars (pattern.type.lam_forall_vars _) _ = Some _ |- _ ]
                           => pose proof (pattern.type.app_forall_vars_lam_forall_vars H); clear H
                         | [ H : Option.bind ?x _ = Some _ |- _ ]
                           => destruct x eqn:?; cbn [Option.bind] in H; [ | solve [ inversion_option ] ]
                         | [ |- expr.interp _ (UnderLets.interp _ (maybe_do_again _ _ _ _)) == _ ]
                           => apply interp_maybe_do_again_gen; [ assumption | ]
                         | [ |- context[rew ?pf in _] ] => is_var pf; destruct pf
                         | [ |- context[(rew [?P] ?pf in ?f) ?x] ]
                           => lazymatch P with
                              | fun t : ?T => ?A -> @?B t
                                => replace ((rew [P] pf in f) x) with (rew [B] pf in f x) by now case pf
                              end
                         end ].

          move Heqo0 at bottom.
          epose proof (pattern.type.app_forall_vars_lam_forall_vars Heqo0).
          eapply pattern.type.app_forall_vars_lam_forall_vars in Heqo0.
          lazymatch goal with
          | [ H : pattern.type.app_forall_vars (pattern.type.lam_forall_vars _) _ = Some _ |- _ ]
            => apply pattern.type.app_forall_vars_lam_forall_vars in H
          end.
          Search (_ (rew _ in _)).
          move u0 at bottom.
          move Hrewr at bottom.
          cbv [rewrite_rule_data_interp_goodT] in *.
          cbv [rew_should_do_again rew_with_opt rew_under_lets rew_replacement] in *.
        Lemma interp_rewrite_with_rule
              (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t))
              (Hdo_again : forall G t e1 e2,
                  (forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 === v2)
                  -> expr.wf G e1 e2
                  -> expr.interp ident_interp (UnderLets.interp ident_interp (do_again t e1)) == expr.interp ident_interp e2)
              (rewr : rewrite_ruleT)
              (Hrewr : rewrite_rule_data_interp_goodT (projT2 rewr))
              t e re v
          : rewrite_with_rule do_again e re rewr = Some v
            -> @rawexpr_equiv_expr t e re
            -> expr.interp ident_interp (UnderLets.interp ident_interp v) == expr.interp ident_interp e.
        Proof using pident_unify_to_typed.
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
                       | progress cbn [Option.bind projT1 projT2 UnderLets.interp eq_rect] in *
                       | progress destruct_head'_sigT
                       | progress destruct_head'_sig
                       | progress inversion_option
                       | progress subst
                       | solve [ intros; inversion_option ]
                       | rewrite !UnderLets.interp_splice
                       | match goal with
                         | [ H : Option.bind ?x _ = Some _ |- _ ]
                           => destruct x eqn:?; cbn [Option.bind] in H; [ | solve [ inversion_option ] ]
                         | [ |- expr.interp _ (UnderLets.interp _ (maybe_do_again _ _ _ _)) == _ ]
                           => apply interp_maybe_do_again_gen; [ assumption | ]
                         | [ |- context[rew ?pf in _] ] => is_var pf; destruct pf
                         end ].
          cbv [rew_should_do_again rew_with_opt rew_under_lets rew_replacement] in *; destruct r; break_innermost_match_step; revgoals.
          move u0 at bottom.
          move Hrewr at bottom.
          cbv [rewrite_rule_data_interp_goodT] in *.
          cbv [rew_should_do_again rew_with_opt rew_under_lets rew_replacement] in *.
          match goal with
          | [ H :
          destruct e0.
          destruct r;
          destruct (rew_should_do_again _ _ r); revgoals.
          match goal with
          end.

          cbv [rewrite_rule_data_interp_goodT] in Hrewr.
          move Hrewr at bottom.
          epose proof (Hrewr _ _) as Hrewr'.
          rewrite Heqo0 in Hrewr'.
          move u at bottom.
          cbv [option_eq related_sigT_by_eq deep_rewrite_ruleTP_gen_good_relation] in Hrewr'.
          revert Hrewr'.
          cbn [projT1 projT2] in *.
          break_innermost_match_step.
          intro.
          let v := open_constr:(Hrewr' _) in specialize v.
          cbn [projT1 projT2] in *.
          destruct_head'_sig; subst.
          cbn [eq_rect] in *.
          break_innermost_match_hyps_step.
          cbn [Option.bind] in *.
          inversion_option; subst.
          rewrite !UnderLets.interp_splice; cbn [UnderLets.interp].
          generalize dependent (match type_of_rawexpr re with type.base t => t | _ => base.type.unit end); intros.
          apply interp_maybe_do_again_gen; [ assumption | ].
          move re at bottom.
          cbv [pattern.pattern_of_anypattern pattern.type_of_anypattern rewrite_ruleTP] in *.
          destruct p as [pt p].
          remember (type.base t) as t' eqn:Ht in *.
          cbv [eq_rect]; break_innermost_match_step.
          cbv [rewrite_rule_data_interp_goodT] in *.



          cbv [deep_rewrite_ruleTP_gen_good_relation] in *.
          cbv [Option.bind] in *; break_inn
                       ].
          rewrite_type_transport_correct; break_match; type_beq_to_eq; cbn [Option.bind] in *; intros; inversion_option; subst; [].
          rewrite !UnderLets.interp_splice; cbn [UnderLets.interp eq_rect]; cbv [id].
          cbn [projT1 projT2] in *.
          generalize dependent (match type_of_rawexpr re with type.base t => t | _ => base.type.unit end); intros.
          apply interp_maybe_do_again_gen; [ assumption | ].
          move re at bottom.
          cbv [pattern.pattern_of_anypattern pattern.type_of_anypattern rewrite_ruleTP] in *.
          destruct p as [pt p].
          remember (type.base t) as t' eqn:Ht in *.
          cbv [eq_rect]; break_innermost_match_step.
          cbv [rewrite_rule_data_interp_goodT] in *.
          (*cbv [rew_is_cps rew_under_lets rew_replacement rew_should_do_again rew_with_opt] in *; destruct r.*)
          destruct Hrewr as [Hrewr1 Hrewr2].
          let H := match goal with H : context[unify_pattern] |- _ => H end in
          revert H.
          cbv [unify_pattern].
          rewrite unify_types_cps_id; unfold Option.bind at 1;
            break_match_step ltac:(fun v => match v with unify_types _ _ _ _ => idtac end);
            [ | intros; exfalso; discriminate ].
          unfold Option.bind at 1;
            break_match_step ltac:(fun v => match v with pattern.type.app_forall_vars _ _ => idtac end);
            [ | intros; exfalso; discriminate ].
          eapply app_under_with_unification_resultT_relation1 in Hrewr1; [ | eassumption ].
          eapply app_under_with_unification_resultT_relation_hetero in Hrewr2.
          lazymatch goal with
          | [ H : ?f = Some _, H' : context[option_eq _ ?f' ?g] |- _ ]
            => unify f f'; change f' with f in H'; rewrite H in H'; cbv [option_eq] in H'; destruct g eqn:?; [ | exfalso; assumption ]
          end.
          cbv beta in *.
          unshelve eapply interp_unify_pattern'_under_with_unification_resultT'_relation_hetero in Hrewr2; [ assumption.. | ].
          rewrite unify_pattern'_cps_id.
          lazymatch goal with
          | [ H : option_eq ?P (@unify_pattern' ?t ?re ?p ?evm ?K ?v ?T (@Some ?T2)) ?X
              |- context G[@unify_pattern' ?t' ?re ?p ?evm ?K' ?v ?T' ?T2'] ]
            => let cst := constr:(@unify_pattern' t re p evm K v T (@Some T2)) in
               let G' := context G[cst] in
               change G'; destruct cst eqn:?, X eqn:?; cbv [option_eq] in H;
                 cbn [Option.bind];
                 inversion_option; try (exfalso; assumption); [ | intro; discriminate ]
          end.
          rewrite_type_transport_correct; break_match_when_head_step (@sumbool);
            type_beq_to_eq; cbn [Option.bind] in *; [ | intro ]; inversion_option; subst; [].
          cbv [id eq_rect] in *.
          break_match_hyps_when_head_step (@eq).
          cbv [deep_rewrite_ruleTP_gen_good_relation id] in Hrewr2.
          lazymatch goal with
          | [ H : normalize_deep_rewrite_rule ?d _ (fun y => y) = Some _, H' : context[normalize_deep_rewrite_rule ?d _ (fun x => x)] |- _ ]
            => rewrite H in H'
          end.
          cbv [rew_is_cps rew_under_lets rew_replacement rew_should_do_again rew_with_opt] in *; destruct r.
          break_innermost_match.
          Focus 2.
          { rewrite Hrewr2.
            eapply interp_unify_pattern'_default_interp; try eassumption.
            apply unify_types_match_with in Heqo.
            move Heqo at bottom.
            move e at bottom.
            exact admit. }
          Unfocus.
          exact admit.
        Qed.

        Lemma interp_eval_rewrite_rules
              (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t))
              (d : decision_tree)
              (rew_rules : rewrite_rulesT)
              (re : rawexpr) (e := expr_of_rawexpr re) v
              (res := @eval_rewrite_rules do_again d rew_rules re)
              (Hdo_again : forall G t e1 e2,
                  (forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 === v2)
                  -> expr.wf G e1 e2
                  -> expr.interp ident_interp (UnderLets.interp ident_interp (do_again t e1)) == expr.interp ident_interp e2)
              (He : rawexpr_equiv_expr e re)
              (Hrew_rules : rewrite_rules_interp_goodT rew_rules)
          : expr.interp ident_interp e == v
            -> expr.interp ident_interp (UnderLets.interp ident_interp res) == v.
        Proof using raw_pident_to_typed_invert_bind_args invert_bind_args_unknown_correct pident_unify_unknown_correct.
          subst res; cbv [eval_rewrite_rules].
          refine (let H := eval_decision_tree_correct d [re] _ in _).
          destruct H as [H| [? [? [H ?] ] ] ]; rewrite H; cbn [Option.sequence Option.sequence_return];
            [ cbn [UnderLets.interp]; exact id | ]; clear H.
          inversion_head' eqlistA.
          unfold Option.bind at 1.
          break_innermost_match_step; [ | cbn [Option.sequence_return UnderLets.interp]; exact id ].
          cbn [Option.bind Option.sequence Option.sequence_return].
          match goal with
          | [ |- _ -> ?R (?f (?g (Option.sequence_return ?x ?y))) _ ]
            => destruct x eqn:Hinterp
          end; cbn [Option.sequence_return UnderLets.interp]; [ | exact id ].
          intro; rewrite interp_rewrite_with_rule; try eassumption.
          { eapply Hrew_rules, nth_error_In; rewrite <- sigT_eta; eassumption. }
          { rewrite rawexpr_equiv_expr_to_rawexpr_equiv;
              split; etransitivity; (idtac + symmetry); eassumption. }
        Qed.

        Lemma interp_assemble_identifier_rewriters'
              (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t))
              (dt : decision_tree)
              (rew_rules : rewrite_rulesT)
              t e v re K
              (res := @assemble_identifier_rewriters' dt rew_rules do_again t re K)
              (HK : { pf : type_of_rawexpr re = t
                    | K = (fun P v => rew [P] pf in v)
                      /\ rew pf in expr_of_rawexpr re = e })
              (Hdo_again : forall G t e1 e2,
                  (forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 === v2)
                  -> expr.wf G e1 e2
                  -> expr.interp ident_interp (UnderLets.interp ident_interp (do_again t e1)) == expr.interp ident_interp e2)
              (Hrew_rules : rewrite_rules_interp_goodT rew_rules)
              (He : rawexpr_equiv_expr e re)
          : expr.interp ident_interp e == v
            -> res === v.
        Proof using raw_pident_to_typed_invert_bind_args_type raw_pident_to_typed_invert_bind_args invert_bind_args_unknown_correct pident_unify_unknown_correct.
          destruct HK as [pf [HK Ke] ]; subst K e; intro Hv.
          subst res; revert dependent re; induction t as [t|s IHs d IHd]; cbn [assemble_identifier_rewriters' value_interp_related1]; intros;
            fold (@type.interp).
          { set (t' := type.base t) in pf, He.
            revert v Hv.
            change (base.interp t) with (type.interp base.interp t').
            change (type.base t) with t'.
            assert (Ht : type.base t = t') by reflexivity.
            clearbody t'.
            destruct pf; cbn [eq_rect] in *; intros.
            eapply interp_eval_rewrite_rules; auto. }
          { cbn [type.related]; cbv [respectful id]; cbn [type_of_rawexpr] in *.
            intros.
            match goal with
            | [ |- assemble_identifier_rewriters' _ _ _ _ ?re _ === _ ]
              => specialize (fun e => IHd e re eq_refl)
            end.
            cbn [type_of_rawexpr eq_rect] in *.
            eapply IHd; cbn [expr_of_rawexpr expr.interp rawexpr_equiv_expr type.related] in *; cbv [respectful rValueOrExpr2] in *.
            all: repeat first [ apply interp_reify
                              | reflexivity
                              | progress cbn [rawexpr_equiv_expr]
                              | match goal with
                                | [ |- and _ _ ] => apply conj
                                | [ H : _ |- _ ] => apply H; clear H
                                end
                              | break_innermost_match_step ]. }
        Qed.
          Local Notation "e1 === e2" := (existT expr _ e1 = existT expr _ e2) : type_scope.
          Local Notation "e1 ==== e2" := (existT (@value' _ _) _ e1 = existT (@value' _ _) _ e2) : type_scope.

          Local Notation maybe_to_expr with_lets
            := (if with_lets as wl return (if wl then _ else _) -> expr _
                then UnderLets.to_expr
                else (fun x => x)).

          Fixpoint rawexpr_equiv_value {t0} (e1 : @value var t0) (r2 : rawexpr) {struct r2} : Prop
            := match r2 with
               | rValue t e => e ==== e1
               | rExpr t e => @reflect _ false _ e ==== e1
               | rIdent _ t idc t' alt
                 => alt === expr.Ident idc
                    /\ expr.Ident idc === @reify _ false _ e1
               | rApp f x t alt
                 => match alt with
                    | expr.App s d f' x'
                      => exists (fv : @value var (s -> d))
                                (xv : @value var s),
                         fv xv ==== Base_value e1
                         /\ f' === @reify _ false _ fv
                         /\ x' === @reify _ false _ xv
                         /\ @rawexpr_equiv_value _ fv f
                         /\ @rawexpr_equiv_value _ xv x
                    | _ => False
                    end
               end.


        Lemma interp_assemble_identifier_rewriters
              (do_again : forall t : base.type, @expr.expr base.type ident value t -> UnderLets (expr t))
              (d : decision_tree)
              (rew_rules : rewrite_rulesT)
              t idc
              (res := @assemble_identifier_rewriters d rew_rules do_again t idc)
              (Hdo_again : forall G t e1 e2,
                  (forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 === v2)
                  -> expr.wf G e1 e2
                  -> expr.interp ident_interp (UnderLets.interp ident_interp (do_again t e1)) == expr.interp ident_interp e2)
              (Hrew_rules : rewrite_rules_interp_goodT rew_rules)
          : res === ident_interp t idc.
        Proof using eta_ident_cps_correct raw_pident_to_typed_invert_bind_args_type raw_pident_to_typed_invert_bind_args invert_bind_args_unknown_correct pident_unify_unknown_correct ident_interp_Proper.
          subst res; cbv [assemble_identifier_rewriters].
          rewrite eta_ident_cps_correct.
          apply interp_assemble_identifier_rewriters' with (e:=expr.Ident idc);
            cbn [type_of_rawexpr rawexpr_equiv_expr expr.interp]; cbv [id eq_rect]; try (exists eq_refl); try apply ident_interp_Proper; eauto.
        Qed.
      End with_interp.

      Section with_cast.
        Context (cast_outside_of_range : ZRange.zrange -> Z -> Z).
        Local Notation var := (type.interp base.interp).
        Local Notation ident_interp := (@ident.gen_interp cast_outside_of_range).
        Local Infix "===" := (@value_interp_related1 ident (@ident_interp) _ _) : type_scope.

        Section with_rewrite_head.
          Context (rewrite_head : forall t (idc : ident t), value_with_lets t)
                  (interp_rewrite_head : forall t idc, rewrite_head t idc === ident_interp idc).

          Lemma interp_rewrite_bottomup G {t e1 e2}
                (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 === v2)
                (Hwf : expr.wf G e1 e2)
            : @rewrite_bottomup var rewrite_head t e1 === expr.interp (@ident_interp) e2.
          Proof using interp_rewrite_head.
            induction Hwf; cbn [rewrite_bottomup expr.interp]; auto.
            all: repeat first [ apply interp_Base_value
                              | progress cbn [value_interp_related1 type.related List.In eq_rect fst snd] in *
                              | progress cbv [respectful LetIn.Let_In] in *
                              | match goal with
                                | [ H : context[rewrite_bottomup] |- @rewrite_bottomup _ _ _ _ === _ ]
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
