Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.WfProofs.
Require Import Crypto.Reflection.MapSigCast.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.HProp.

Section language.
  Context {base_type_code : Type}
          {interp_base_type_bounds : base_type_code -> Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (interp_op_bounds : forall src dst, op src dst -> interp_flat_type interp_base_type_bounds src -> interp_flat_type interp_base_type_bounds dst)
          (pick_typeb : forall t, interp_base_type_bounds t -> base_type_code)
          (base_type_code_beq : base_type_code -> base_type_code -> bool)
          (base_type_code_bl_transparent : forall a b, base_type_code_beq a b = true -> a = b)
          (failv : forall {var t}, @exprf base_type_code op var (Tbase t)).

  Local Notation pick_type
    := (@SmartFlatTypeMap _ _ pick_typeb).

  Context (cast_op : forall ovar t1 tR opc args_bs
                            (argsv : exprf base_type_code op (var:=ovar) (pick_type args_bs)),
              exprf base_type_code op (var:=ovar) (pick_type (interp_op_bounds t1 tR opc args_bs))).

  Context (wff_failv : forall var1 var2 G t, wff G (@failv var1 t) (@failv var2 t)).

  Context (wff_cast_op
           : forall ovar1 ovar2 G t tR opc bs args0 args1,
              wff G args0 args1
              -> wff G (cast_op ovar1 t tR opc bs args0) (cast_op ovar2 t tR opc bs args1)).

  Local Notation SmartFail
    := (SmartValf _ (@failv _)).
  Local Notation failf t (* {t} : @exprf base_type_code1 op1 ovar t*)
    := (SmartPairf (SmartFail t)).
  Local Notation cast_exprf
    := (@cast_exprf _ op _ base_type_code_bl_transparent failv).

  Lemma wff_failf {var1 var2 t} G
    : wff (var1:=var1) (var2:=var2) G (failf t) (failf t).
  Proof.
    induction t;
      repeat first [ apply wff_failv
                   | progress simpl in *
                   | rewrite SmartPairf_Pair
                   | solve [ auto ]
                   | constructor ].
  Qed.

  Lemma wff_cast_exprf {var1 var2 G A B e1 e2}
        (Hwf : wff G e1 e2)
    : wff G (@cast_exprf var1 A B e1) (@cast_exprf var2 A B e2).
  Proof.
    unfold cast_exprf, cast_or; break_innermost_match; auto using wff_failf.
  Qed.

  Local Notation ivarP ovar t
    := (fun bs : interp_flat_type interp_base_type_bounds t
        => @exprf base_type_code op ovar (pick_type bs))%type.
  Local Notation ivar ovar t := (sigT (ivarP ovar t)) (only parsing).
  Local Notation ivarf ovar := (fun t => ivar ovar (Tbase t)).
  Section with_var_let_in.
    Context (let_in : forall ovar T t'
                             (A:=(interp_flat_type (ivarf ovar) T -> @exprf base_type_code op ovar t')%type)
                             (B:=@exprf base_type_code op ovar t'),
                A -> (A -> B) -> B).

    Context (let_in_correct : forall ovar T t' a f, let_in ovar T t' a f = f a).

    Local Notation mapf_cast
      := (@mapf_cast _ _ _ interp_op_bounds pick_typeb _ base_type_code_bl_transparent
                     failv cast_op _ (let_in _)).
    Local Notation map_cast
      := (@map_cast _ _ _ interp_op_bounds pick_typeb _ base_type_code_bl_transparent
                    failv cast_op _ (let_in _)).

    Local Notation cast_expr_pf pf v
      := (eq_rect _ (fun bs => exprf _ _ (pick_type bs)) v _ pf).

    Section with_var.
      Context {ovar1 ovar2 : base_type_code -> Type}.

      Local Hint Constructors wff.

      Lemma wff_mapf_cast_sig
            {t} Gin Gout
            (HG : forall t x y,
                List.In (existT _ t (x, y)) Gin
                -> exists pf : projT1 x = projT1 y,
                  wff Gout (cast_expr_pf pf (projT2 x)) (projT2 y))
            (e1 : @exprf base_type_code op (ivarf ovar1) t)
            (e2 : @exprf base_type_code op (ivarf ovar2) t)
            (Hwf : wff Gin e1 e2)
        : { pf : projT1 (mapf_cast e1) = projT1 (mapf_cast e2)
          | wff (var1:=ovar1) (var2:=ovar2)
                Gout
                (cast_expr_pf pf (projT2 (mapf_cast e1)))
                (projT2 (mapf_cast e2)) }.
      Proof.
        Set Ltac Profiling.
        revert dependent Gout; induction Hwf; intros;
          repeat match goal with
                 | [ IHHwf : forall (Gout' : list ?T), _, Gout : list ?T, HG : forall t x y, List.In _ _ -> exists pf, wff Gout _ _ |- _ ]
                   => unique pose proof (IHHwf Gout HG)
                 end;
          repeat first [ assumption
                       | exists eq_refl
                       | progress intros
                       | progress subst
                       | progress destruct_head' ex
                       | progress destruct_head' sigT
                       | progress destruct_head' sig
                       | progress destruct_head' and
                       | progress inversion_prod
                       | progress destruct_head' prod
                       | progress simpl in *
                       | solve [ constructor | auto | apply wff_failv ]
                       | progress cbv [LetIn.Let_In fail_with_bounds] in *
                       | rewrite let_in_correct 
                       | match goal with
                         | [ H : (forall x y (Gout' : list ?T), (forall t x' y', List.In _ _ -> _) -> { pf : projT1 (?f1 (?e1 x)) = projT1 (?f2 (?e2 y)) | wff Gout' _ _ })
                             |- { pf' : projT1 (?f1 (?e1 ?xv)) = projT1 (?f2 (?e2 ?yv)) | wff ?Gout _ _ } ]
                           => unique pose proof (H xv yv Gout);
                              destruct (f1 (e1 xv)) eqn:?, (f2 (e2 yv)) eqn:?
                         | [ H : (forall x1 x2 Gout, (forall t x y, _) -> { pf : projT1 (?f1 (?e1 x1)) = projT1 (?f2 (?e2 x2)) | wff Gout _ _ })
                             |- wff (_ ++ ?Gout') ?A ?B ]
                           => let x1v := lazymatch A with context[f1 (e1 ?xv)] => xv end in
                              let x2v := lazymatch B with context[f2 (e2 ?xv)] => xv end in
                              unique pose proof (H x1v x2v Gout');
                              destruct (f1 (e1 x1v)) eqn:?, (f2 (e2 x2v)) eqn:?
                         | [ H : forall t x y, List.In _ ?G -> _,
                               H' : (forall t x y, _ \/ List.In _ ?G -> _) -> _
                               |- _ ]
                           => specialize (fun H'' => H' (fun t x y pf => match pf with
                                                                         | or_introl pf' => H'' t x y pf'
                                                                         | or_intror pf' => H t x y pf'
                                                                         end));
                              let T := match type of H' with ?T -> _ => T end in
                              let H'' := fresh in
                              assert (H'' : T); [ clear H' | specialize (H' H'') ]
                         | [ H0 : ?x = ?y :> bool, H1 : ?x = ?y |- _ ]
                           => assert (H0 = H1) by apply allpath_hprop; subst H1
                         | [ H : ?x = eq_refl |- context[?x] ] => rewrite H
                         | [ |- context[let 'existT a b := ?v in _] ]
                           => rewrite (sigT_eta v)
                         | [ |- wff _ (Pair _ _) (Pair _ _) ] => constructor
                         | [ |- wff _ (LetIn _ _) (LetIn _ _) ] => constructor
                         | [ H : _ = projT1 ?x |- _ ]
                           => destruct x eqn:?; simpl in H
                         | [ H : context[List.In _ (List.app _ _)] |- _ ]
                           => setoid_rewrite List.in_app_iff in H
                         | [ H : context[flatten_binding_list (SmartVarfMap _ _) (SmartVarfMap _ _)] |- _ ]
                           => rewrite flatten_binding_list_SmartVarfMap in H
                         | [ H : context[List.In _ (List.map _ _)] |- _ ]
                           => rewrite List.in_map_iff in H
                         | [ H : existT _ _ _ = existT _ _ _ |- _ ]
                           => induction_sigma_in_using H @path_sigT_rect
                         | [ |- wff _ (cast_exprf _) (cast_exprf _) ] => apply wff_cast_exprf
                         | [ H : List.In (existT _ _ (?a, ?b)) (flatten_binding_list ?x ?y) |- _ ]
                           => first [ constr_eq a b; fail 1
                                    | pose proof (flatten_binding_list_same_in_eq H); progress subst ]
                         | [ H : wff _ ?x ?y |- wff _ ?x ?y ]
                           => solve [ eapply wff_in_impl_Proper; eauto using List.in_or_app ]
                         end
                       | match goal with
                         | [ H : List.In _ _, H' : forall t x y, List.In _ _ -> _ |- _ ]
                           => apply H' in H
                         | [ |- exists pf : ?x = ?y, _ ]
                           => is_var x; is_var y;
                              let H := fresh in
                              cut (x = y);
                              [ intro H; exists H; subst y | ]
                         end ].
        Show Ltac Profile.
        move e6 at bottom.
        move x0 at bottom.
        match goal with
        end.
        move e4 at bottom.
        { match goal with
          end.
          unfold cast_exprf at 1 3.

          unfold cast_or.
          cbv [cast_exprf cast_or] in *; break_innermost_match;
            repeat match goal with
                   | [ H0 : ?x = ?y :> bool, H1 : ?x = ?y |- _ ]
                     => assert (H0 = H1) by apply allpath_hprop; subst H1
                   | [ H : ?x = eq_refl |- context[?x] ] => rewrite H
                   | _ => assumption
                   | _ => solve [ eapply wff_in_impl_Proper; eauto using List.in_or_app | apply wff_failf ]
                   end.

          .
          move x1 at bottom.
          move x3 at bottom.
          SearchAbout List.In List.app.
          eapply Proper_impl
          rewrite_hyp !*.
        Focus 2.
        move x5 at bottom.
        move x6 at bottom.
        move x2 at bottom.
        move e2 at bottom.
        match goal with
        end.
        Focus 2.
        move x0 at bottom.
        move x2 at bottom.
        clear Heqe4 H1.
        match goal with
        end.
                  repeat first [ assumption
                       | exists eq_refl
                       | progress intros
                       | progress subst
                       | progress simpl in *
                       | progress destruct_head ex
                       | progress destruct_head sigT
                       | progress destruct_head sig
                       | progress destruct_head and
                       | progress inversion_prod
                       | progress destruct_head prod
                       | solve [ constructor | auto | apply wff_failv ]
                       | progress cbv [LetIn.Let_In fail_with_bounds] in *
                       | rewrite let_in_correct
                       | match goal with
                         | [ H : (forall x y (Gout' : list ?T), (forall t x' y', List.In _ _ -> _) -> { pf : projT1 (?f1 (?e1 x)) = projT1 (?f2 (?e2 y)) | wff Gout' _ _ })
                             |- { pf' : projT1 (?f1 (?e1 ?xv)) = projT1 (?f2 (?e2 ?yv)) | wff ?Gout _ _ } ]
                           => unique pose proof (H xv yv Gout);
                              destruct (f1 (e1 xv)) eqn:?, (f2 (e2 yv)) eqn:?
                         | [ H : forall t x y, List.In _ ?G -> _,
                               H' : (forall t x y, _ \/ List.In _ ?G -> _) -> _
                               |- _ ]
                           => specialize (fun H'' => H' (fun t x y pf => match pf with
                                                                         | or_introl pf' => H'' t x y pf'
                                                                         | or_intror pf' => H t x y pf'
                                                                         end));
                              let T := match type of H' with ?T -> _ => T end in
                              let H'' := fresh in
                              assert (H'' : T); [ clear H' | specialize (H' H'') ]
                         | [ H0 : ?x = ?y :> bool, H1 : ?x = ?y |- _ ]
                           => assert (H0 = H1) by apply allpath_hprop; subst H1
                         | [ |- context[let 'existT a b := ?v in _] ]
                           => rewrite (sigT_eta v)
                         | [ |- wff _ (Pair _ _) (Pair _ _) ] => constructor
                         | [ |- wff _ (LetIn _ _) (LetIn _ _) ] => constructor
                         | [ H : _ = projT1 ?x |- _ ]
                           => destruct x eqn:?; simpl in H
                         | [ H : context[List.In _ (List.app _ _)] |- _ ]
                           => setoid_rewrite List.in_app_iff in H
                         | [ H : _ |- _ ] => rewrite flatten_binding_list_SmartVarfMap in H
                         | [ H : context[List.In _ (List.map _ _)] |- _ ]
                           => rewrite List.in_map_iff in H
                         | [ H : existT _ _ _ = existT _ _ _ |- _ ]
                           => induction_sigma_in_using H @path_sigT_rect
                         | [ H : List.In (existT _ _ (?a, ?b)) (flatten_binding_list ?x ?y) |- _ ]
                           => first [ constr_eq a b; fail 1
                                    | pose proof (flatten_binding_list_same_in_eq H); progress subst ]
                         end
                       | match goal with
                         | [ H : List.In _ _, H' : forall t x y, List.In _ _ -> _ |- _ ]
                           => apply H' in H
                         | [ |- exists pf : ?x = ?y, _ ]
                           => is_var x; is_var y;
                              let H := fresh in
                              cut (x = y);
                              [ intro H; exists H; subst y | ]
                         end
                       | progress cbv [cast_exprf cast_or] in *
                       | progress break_innermost_match_step ].
        .
        SearchAbout (_ = _ :> (_ = _ :> bool)).
        match
        break_innermost_match_step.
        break_innermost_match_step.
        lazymatch goal with
        end.

        SearchAbout (flatten_binding_list ?x ?x).
        { .
        SearchAbout wff SmartPairf.
        match goal with
        end.
        match goal with
        end.
        SearchAbout List.In List.map.
        SearchAbout flatten_binding_list SmartVarfMap.

        match goal with
        end.
        Print fail_with_bounds.
        match goal with
        end.
        end.
        exfalso.
        clear -HG.
        clear HG.
        Goal ((forall (t : Set) (x y : t),
                  True ->
                  x = y)) -> False.
          clear; intro HG.
        lazymatch goal with
        | [ H : (forall t x y, True -> _)
              |- _ ]
          => idtac H
        end.
        lazymatch goal with
        | [ H : forall t x y, True -> @?P t x y
              |- _ ]
          => idtac
        end.
                   en
        SearchAbout List.In List.app.
        match goal with
        end.
        move e2 at bottom.
                  repeat first [ assumption
                       | exists eq_refl
                       | progress intros
                       | progress subst
                       | progress simpl in *
                       | progress destruct_head ex
                       | progress destruct_head sigT
                       | progress destruct_head sig
                       | solve [ constructor | auto ]
                       | progress cbv [LetIn.Let_In] in *
                       | match goal with
                         | [ H : (forall x y (Gout' : list ?T), (forall t x' y', List.In _ _ -> _) -> { pf : projT1 (?f1 (?e1 x)) = projT1 (?f2 (?e2 y)) | wff Gout' _ _ })
                             |- { pf' : projT1 (?f1 (?e1 ?xv)) = projT1 (?f2 (?e2 ?yv)) | wff ?Gout _ _ } ]
                           => specialize (H xv yv Gout)
                         | [ |- context[let 'existT a b := ?v in _] ]
                           => rewrite (sigT_eta v)
                         | [ |- wff _ (Pair _ _) (Pair _ _) ] => constructor
                         end ].
                  match goal with
                  end.
                  specialize (fun x1 x2 => H0 x1 x2 Gout).

        simpl.
        move x1 at bottom.
        move x3 at bottom.
        move e0 at bottom.
        move e4 at bottom.
        Focus 2.
        revert w.
        clear.
        revert e0 e1.
        intros args0 args1; revert args0 args1.
        rename x1 into bs; revert bs.
        rename op0 into opc; revert opc.
        revert t tR.
        rename Gout into G; revert G.
        revert ovar1 ovar2.

        revert bs.
        revert x1
        move x at bottom.
        move x0 at bottom.


        { simpl; exists eq_refl; simpl; constructor. }
        { simpl; intros.

    Fixpoint mapf_cast
             {t} (e : @exprf base_type_code op ivarf t)
             {struct e}
      : ivar t
      := match e in exprf _ _ t return ivar t with
         | TT => existT _ tt TT
         | Var t v => v
         | Pair tx ex ty ey
           => let 'existT x_bs xv := @mapf_cast _ ex in
              let 'existT y_bs yv := @mapf_cast _ ey in
              existT _ (x_bs, y_bs) (Pair xv yv)
         | LetIn tx ex tC eC
           => dlet Cv := (fun v => @mapf_cast _ (eC v)) in
               let 'existT x_bs xv := @mapf_cast _ ex in
               let 'existT Cfail_bs _ := Cv (fail_with_bounds x_bs) in
               existT
                 _
                 Cfail_bs
                 (let_in
                    _ (pick_type Cfail_bs)
                    (fun v => cast_exprf (projT2 (Cv v)))
                    (fun Cv'
                     => LetIn xv
                              (fun v => cast_exprf (Cv' (existT_ivar x_bs v)))))
                       | Op t1 tR opc args
                         => let 'existT args_bs argsv := @mapf_cast _ args in
                            existT
                              _
                              (interp_op_bounds _ _ opc args_bs)
                              (cast_op _ _ _ opc args_bs argsv)
         end%core.
    Definition map_cast
             {t} (e : @expr base_type_code op ivarf t)
             (in_bounds : interp_flat_type interp_base_type_bounds (domain t))
      : { out_bounds : interp_flat_type interp_base_type_bounds (codomain t)
                       & @expr base_type_code op ovar (Arrow (pick_type in_bounds) (pick_type out_bounds)) }
      := dlet f := (fun v => mapf_cast (invert_Abs e v)) in
         let 'existT f_fail_bs _ := f (fail_with_bounds in_bounds) in
         existT
           _
           f_fail_bs
           (Abs
              (fun x
               => let_in
                    _ (pick_type f_fail_bs)
                    (fun v => cast_exprf (projT2 (f v)))
                    (fun f' => f' (existT_ivar _ x)))).
  End with_var.

  Definition MapCast
             (let_in : forall A B, A -> (A -> B) -> B)
             {t} (e : @Expr base_type_code op t)
             (in_bounds : interp_flat_type interp_base_type_bounds (domain t))
    : { out_bounds : interp_flat_type interp_base_type_bounds (codomain t)
                     & forall var, @expr base_type_code op var (Arrow (pick_type in_bounds) (pick_type out_bounds)) }
    := dlet f := (fun ovar => @map_cast ovar (fun _ _ => let_in _ _) t (e _) in_bounds) in
       let 'existT bs _ := f interp_base_type_bounds in
       existT
         _
         bs
         (fun ovar
          => let_in
               _ _ (fun ovar => cast_expr (projT2 (f ovar)))
               (fun f' => f' ovar)).
End language.

Global Arguments mapf_cast {_ _ _} interp_op_bounds pick_typeb {_} base_type_code_bl_transparent failv cast_op {ovar} let_in {t} e.
Global Arguments map_cast {_ _ _} interp_op_bounds pick_typeb {_} base_type_code_bl_transparent failv cast_op {ovar} let_in {t} e.
Global Arguments MapCast {_ _ _} interp_op_bounds pick_typeb {_} base_type_code_bl_transparent failv cast_op let_in {t} e.
