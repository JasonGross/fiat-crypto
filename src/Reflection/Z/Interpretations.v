(** * Interpretation of PHOAS syntax for expression trees on ℤ *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Z.Syntax.Util.
Require Import Crypto.Reflection.Z.OpInversion.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Z.BoundsInterpretations.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.InterpWfRel.
Require Import Crypto.Reflection.WfProofs.
Require Import Crypto.Reflection.WfInversion.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Reflection.TypeInversion.
Require Import Crypto.Reflection.Linearize.
Require Import Crypto.Reflection.LinearizeInterp.
Require Import Crypto.Reflection.LinearizeWf.
Require Import Crypto.Reflection.Inline.
Require Import Crypto.Reflection.InlineInterp.
Require Import Crypto.Reflection.Equality.
Require Import Crypto.Reflection.MapCast.
Require Import Crypto.Reflection.MapCastInterp.
Require Import Crypto.Reflection.MapCastWf.
Require Import Crypto.Reflection.Eta.
Require Import Crypto.Reflection.EtaInterp.
Require Import Crypto.Reflection.SmartBound.
Require Import Crypto.Reflection.SmartCast.
Require Import Crypto.Reflection.SmartCastWf.
Require Import Crypto.Reflection.BoundByCast.
Require Import Crypto.Reflection.BoundByCastWf.
Require Import Crypto.Reflection.BoundByCastInterp.
Require Import Crypto.ModularArithmetic.ModularBaseSystemListZOperations.
Require Import Crypto.Util.Equality.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Option.
Require Crypto.Util.Tuple.
Require Crypto.Util.HList.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.
Require Import Bedrock.Word.
Require Import Crypto.Util.WordUtil.
Require Import Crypto.Util.FixedWordSizesEquality.
Export Reflection.Syntax.Notations.

Local Notation eta x := (fst x, snd x).
Local Notation eta3 x := (eta (fst x), snd x).
Local Notation eta4 x := (eta3 (fst x), snd x).

Module Import Bounds.
  Import BoundsInterpretations.Bounds.
  Import Bounds.Notations.

  Definition ComputeBounds {t} (e : Expr base_type op t)
             (input_bounds : interp_flat_type Bounds.interp_base_type (domain t))
    : interp_flat_type Bounds.interp_base_type (codomain t)
    := Interp (@Bounds.interp_op) e input_bounds.

  Definition map_uncast_const {t} (bounds : interp_flat_type Bounds.interp_base_type t) (e : interp_flat_type Syntax.interp_base_type _)
    : interp_flat_type Syntax.interp_base_type t
    := interpf_smart_unbound
         Bounds.interp_base_type (fun _ => @Bounds.bounds_to_base_type)
         (@cast_const)
         bounds e.

  Local Notation bound_base_type t := Bounds.bounds_to_base_type (only parsing).

  Local Hint Extern 1 => progress simpl.
  Local Hint Extern 1 (_ = _) => reflexivity.
  Local Hint Resolve cast_const_id @cast_const_idempotent.
  Local Arguments Z.pow_pos !_ !_ / .
  Local Arguments Z.add !_ !_.
  Section with_rewrite_le.
    Local Existing Instances Z.add_le_Proper Z.sub_le_eq_Proper Z.log2_up_le_Proper Z.pow_Zpos_le_Proper.
    Lemma strip_cast_const t x y
      : @Bounds.is_bounded_by' t y x
        -> @cast_const (bound_base_type t x) t (@cast_const t (bound_base_type t x) y) = y.
    Proof.
      unfold Bounds.is_bounded_by', Bounds.is_bounded_byb, cast_const, ZToInterp, interpToZ.
      repeat first [ progress subst
                   | reflexivity
                   | congruence
                   | progress destruct_head_hnf' option
                   | progress destruct_head_hnf' bounds
                   | progress destruct_head_hnf' base_type
                   | progress Z.ltb_to_lt
                   | progress split_andb
                   | progress unfold bounds_to_base_type' in *
                   | progress intros
                   | match goal with
                     | [ H : TWord _ = TWord _ |- _ ] => inversion H; clear H
                     | [ |- (?x < ?y)%Z ]
                       => cut (x <= y - 1)%Z; [ omega | ]
                     end
                   | progress rewrite ?wordToZ_ZToWord, ?ZToWord_wordToZ, ?ZToWord_gen_wordToZ_gen, ?Z.pow_Zpow
                   | rewrite Z2Nat.id by auto with zarith
                   | progress break_innermost_match_step
                   | progress break_match_hyps
                   | rewrite <- !Z.log2_up_le_full
                   | progress simpl in *
                   | omega
                   | split; [ reflexivity || omega | ] ].
    Qed.
  End with_rewrite_le.

  Local Notation bound_op := (@bound_op _ _ _ (@Bounds.interp_op) (fun t => bound_base_type t) _ internal_base_type_dec_bl base_type_leb (@Castb) genericize_op).
  Local Notation G_invariant_holds G
    := (forall t x x',
           List.In (existT _ t (x, x')%core) G -> @is_bounded_by' t x x')
         (only parsing).

  Section bounded_by_interp_op.
    Local Notation is_bounded_by_interp_opT opc
      := (forall t sv1 sv2,
             is_bounded_by sv1 sv2
             -> is_bounded_by (Syntax.interp_op _ _ (opc t) sv1) (interp_op (opc t) sv2))
           (only parsing).
    Local Notation is_bounded_by_bound_opT opc
      := (forall
             t G ein eout ebounds
             (Hwf : wff G ein ebounds)
             (HG : G_invariant_holds G)
             (Hinout : interpf Syntax.interp_op ein = interpf Syntax.interp_op eout)
             (Hrgood : bounds_are_recursively_good (@Bounds.interp_op) bound_is_good ebounds)
             (Hgood : bounds_are_good (@Bounds.interp_op _ _ (opc t) (interpf (@Bounds.interp_op) ebounds))),
             is_bounded_by
               (interpf Syntax.interp_op (@bound_op Syntax.interp_base_type _ _ _ _ (opc t) (opc t) eout (interpf (@Bounds.interp_op) ebounds)))
               (interpf (@Bounds.interp_op) (Op (opc t) ebounds)))
           (only parsing).

    Local Notation interpf_bound_opT opc
      := (forall t G ein eout ebounds
                 (Hwf : wff G ein ebounds)
                 (HG : G_invariant_holds G)
                 (Hinout : interpf Syntax.interp_op ein = interpf Syntax.interp_op eout)
                 (Hrgood : bounds_are_recursively_good (@Bounds.interp_op) bound_is_good ebounds)
                 (Hgood : bounds_are_good (@Bounds.interp_op _ _ (opc t) (interpf (@Bounds.interp_op) ebounds))),
             interpf Syntax.interp_op (@bound_op Syntax.interp_base_type _ _ _ _ (opc t) (opc t) eout (interpf (@Bounds.interp_op) ebounds))
             = interpf Syntax.interp_op (Op (opc t) ein))
           (only parsing).

    Local Ltac fin_t :=
      first [ reflexivity
            | omega
            | match goal with |- context[(_ * _)%Z] => idtac end;
              nia ].

    Local Ltac intro_t :=
      first [ progress simpl in *
            | progress intros ].

    Local Ltac break1_t :=
      first [ progress subst
            | progress destruct_head_hnf' unit
            | progress inversion_bounds
            | progress inversion_option
            | progress destruct_head' and
            | progress destruct_head' prod
            | progress destruct_head_hnf' bounds
            | progress split_andb
            | progress split_and ].
    Local Ltac break2_t :=
      first [ progress destruct_head' base_type
            | progress destruct_head_hnf' option
            | progress destruct_head' or
            | progress break_innermost_match_step ].
    Local Ltac unfolder_t :=
      first [ progress unfold is_bounded_by', is_bounded_byb in *
            | progress unfold SmartBuildBounds, SmartVarfMap in *
            | progress unfold neg, cmovle, cmovne in *
            | progress unfold ModularBaseSystemListZOperations.wneg, ModularBaseSystemListZOperations.neg, ModularBaseSystemListZOperations.wcmovne, ModularBaseSystemListZOperations.cmovne, ModularBaseSystemListZOperations.wcmovl, ModularBaseSystemListZOperations.cmovl in * ].
    Local Ltac late_unfolder_t :=
      first [ progress unfold wneg_gen, wcmovl_gen, wcmovne_gen in * ].

    (* split the goal, but only if it's about Z, not word *)
    Local Ltac Z_andb_splitter_t :=
      lazymatch goal with
      | [ sz : nat |- _ ] => fail
      | [ w : FixedWordSizes.wordT _ |- _ ] => fail
      | [ w : word _ |- _ ] => fail
      | [ |- andb _ _ = true ] => apply Bool.andb_true_iff, conj
      end.

    Local Ltac rewriter1_t :=
      match goal with
      | [ H : true = true |- _ ] => clear H
      | [ H : ?x = true, H' : context[?x] |- _ ] => rewrite H in H'
      | [ H : ?x = true |- context[?x] ] => rewrite H
      | _ => rewrite Bool.andb_true_r
      | _ => rewrite Bool.andb_true_l
      | [ H : andb _ _ = false |- _ ] => apply Bool.andb_false_iff in H
      | _ => rewrite wordToZ_gen_ZToWord_gen
          by (rewrite ?Z.pow_Zpow; eauto using Z.ones_nonneg, (fun a b pf => proj2 (Z.log2_lt_pow2_alt a b pf)), Z.le_lt_trans, Z.log2_nonneg with omega)
      | _ => rewrite wordToZ_ZToWord
          by (rewrite ?Z.pow_Zpow; eauto using Z.ones_nonneg, (fun a b pf => proj2 (Z.log2_lt_pow2_alt a b pf)), Z.le_lt_trans, Z.log2_nonneg with omega)
      end.

    Local Ltac Zltb_to_lt :=
      first [ progress Z.ltb_to_lt
            | match goal with
              | [ |- ((_ <=? _) && (_ <=? _))%Z%bool = true ]
                => rewrite Bool.andb_true_iff, !Z.leb_le
              end ].

    Local Ltac simpler_t :=
      first [ progress specialize_by auto
            | match goal with
              | [ H : context[Z.of_N (wordToN ?x)] |- _ ]
                => change (Z.of_N (wordToN x)) with (FixedWordSizes.wordToZ_gen x) in *
              | [ |- context[Z.of_N (wordToN ?x)] ]
                => change (Z.of_N (wordToN x)) with (FixedWordSizes.wordToZ_gen x) in *
              | [ H : (?x <= ?x)%Z |- _ ] => clear H
              | [ H : FixedWordSizes.wordToZ ?x = _ |- _ ]
                => generalize dependent (FixedWordSizes.wordToZ x); clear x; intros; subst
              | [ H : _ = FixedWordSizes.wordToZ ?x |- _ ]
                => generalize dependent (FixedWordSizes.wordToZ x); clear x; intros; subst
              end ].

    Local Ltac misc_solver_t :=
      solve [ eauto using Z.shiftl_le_mono, Z.shiftr_le_mono, Z.ones_nonneg with nocore omega
            | apply Z.land_nonneg; eauto with nocore omega
            | apply Z.min_case_strong;
              eauto using Z.land_upper_bound_r, Z.land_upper_bound_l, Z.le_trans with nocore omega
            | apply Z.lor_bounds_gen_lower; eauto using Z.max_le_compat with omega
            | autorewrite with push_Zmax;
              apply Z.lor_bounds_gen_upper; eauto using Z.le_max_l, Z.le_max_r, Z.le_trans with omega
            | apply Z.max_case_strong; omega ].

    Local Ltac t_step :=
      first [ fin_t
            | intro_t
            | break1_t
            | unfolder_t
            | rewriter1_t
            | simpler_t
            | Z_andb_splitter_t
            | break2_t
            | Zltb_to_lt
            | progress adjust_mbs_wops
            | misc_solver_t
            | progress syntactic_fixed_size_op_to_word
            | late_unfolder_t ].
    Local Ltac t := repeat t_step.

    Local Ltac precutZ :=
      let G := match goal with |- forall t, @?G t => G end in
      let t := fresh in
      intro t;
      cut (G TZ);
      [ destruct t; [ solve [ trivial ]
                    | ]
      | clear t ].
    Local Ltac cutZ :=
      precutZ;
      [ let H := fresh in
        let b := fresh in
        let v := fresh in
        intros H v b;
        specialize (H (SmartVarfMap (fun _ => interpToZ) v) b)
      | ].

    Lemma add_is_bounded_by_interp_op : is_bounded_by_interp_opT Add.
    Proof. cutZ; t. split; eapply wadd_valid_update; eauto. Qed.
    Local Hint Resolve add_is_bounded_by_interp_op.
    Lemma sub_is_bounded_by_interp_op : is_bounded_by_interp_opT Sub.
    Proof. cutZ; t. split; eapply wsub_valid_update; eauto. Qed.
    Local Hint Resolve sub_is_bounded_by_interp_op.
    Lemma mul_is_bounded_by_interp_op : is_bounded_by_interp_opT Mul.
    Proof. cutZ; t. split; eapply wmul_valid_update; eauto. Qed.
    Local Hint Resolve mul_is_bounded_by_interp_op.
    Lemma shl_is_bounded_by_interp_op : is_bounded_by_interp_opT Shl.
    Proof. cutZ; t. split; eapply wshl_valid_update; eauto. Qed.
    Local Hint Resolve shl_is_bounded_by_interp_op.
    Lemma shr_is_bounded_by_interp_op : is_bounded_by_interp_opT Shr.
    Proof. cutZ; t. split; eapply wshr_valid_update; eauto. Qed.
    Local Hint Resolve shr_is_bounded_by_interp_op.
    Lemma land_is_bounded_by_interp_op : is_bounded_by_interp_opT Land.
    Proof. cutZ; t. split; eapply wland_valid_update; eauto with omega. Qed.
    Local Hint Resolve land_is_bounded_by_interp_op.
    Lemma lor_is_bounded_by_interp_op : is_bounded_by_interp_opT Lor.
    Proof. cutZ; t. split; eapply wlor_valid_update; eauto. Qed.
    Local Hint Resolve lor_is_bounded_by_interp_op.
    Lemma neg_is_bounded_by_interp_op int_size : is_bounded_by_interp_opT (fun T => Neg T int_size).
    Proof. cutZ; t. Qed.
    Local Hint Resolve neg_is_bounded_by_interp_op.
    Lemma cmovne_is_bounded_by_interp_op : is_bounded_by_interp_opT Cmovne.
    Proof. cutZ; t. Qed.
    Local Hint Resolve cmovne_is_bounded_by_interp_op.
    Lemma cmovle_is_bounded_by_interp_op : is_bounded_by_interp_opT Cmovle.
    Proof. cutZ; t. Qed.
    Local Hint Resolve cmovle_is_bounded_by_interp_op.
    Lemma cast_is_bounded_by_interp_op T : is_bounded_by_interp_opT (Cast T).
    Proof. t. Qed.
    Local Hint Resolve cast_is_bounded_by_interp_op.

    Lemma is_bounded_by_interp_op src dst (op : op src dst)
      : forall (sv1 : interp_flat_type Syntax.interp_base_type src)
               (sv2 : interp_flat_type interp_base_type src)
               (H : is_bounded_by sv1 sv2),
        is_bounded_by (Syntax.interp_op src dst op sv1) (interp_op op sv2).
    Proof.
      destruct op; auto.
      { (* const casse *) t. }
    Qed.

    Local Hint Resolve @is_bounded_by_interp_op.

    Local Ltac misc_t_2 :=
      match goal with
      | [ H : _ = _ :> prod _ _ |- _ ]
        => pose proof (f_equal (@fst _ _) H);
           pose proof (f_equal (@snd _ _) H);
           clear H
      end.

    Local Ltac inequality_t :=
      match goal with
      | _ => rewrite Z.pow_Zpow
      | _ => rewrite Z2Nat.id by auto using Z.log2_up_nonneg
      | [ |- (_ <= _ < _)%Z ]
        => split; [ solve [ fin_t ] | ]
      | [ |- (?x < ?y)%Z ]
        => cut (x <= y - 1)%Z; [ omega | ]
      | _ => rewrite <- !Z.log2_up_le_full
      end.

    Section with_le_instances.
      Local Arguments Z.add !_ !_.
      Local Existing Instances Z.add_le_Proper Z.sub_le_eq_Proper Z.log2_up_le_Proper Z.pow_Zpos_le_Proper.

      Lemma add_is_bounded_by_bound_op : is_bounded_by_bound_opT Add.
      Proof. precutZ.
             intros H G ein eout ebounds Hwf HG Hinout Hrgood Hgood;
               specialize (H G);
               revert dependent ein; intro ein; revert dependent eout; intro eout;
                 revert dependent ebounds; revert ein eout;
                   do 3 (intro;
                         let e := lazymatch goal with e : _ |- _ => e end in
                         let TZ := match type of H with forall a : exprf _ _ ?T, _ => T end in
                         let TW := match type of e with exprf _ _ ?T => T end in
                         specialize (H (LetIn e
                                              (invert_Some (@SmartCast.SmartCast _ op _ internal_base_type_dec_bl (@Castb) _ TW TZ)))));
                   intros.
             let T := match type of H with ?T -> _ => T end in
             let H' := fresh in
             assert (H' : T); [ | specialize (H H'); clear H' ].
             { constructor; auto; intros.
               eapply wff_in_impl_Proper.
               { lazymatch goal with
                 | [ |- wff (var1:=?var1) (var2:=?var2) ?G
                            (invert_Some (SmartCast _ _ _ ?TW ?TZ) ?x)
                            (invert_Some (SmartCast _ _ _ ?TW ?TZ) ?y) ]
                   => exact (@wff_SmartCast_match _ op _ internal_base_type_dec_bl (@Castb) (@wff_Castb) var1 var2 TW TZ x y)
                 end. }
               { intros; rewrite List.in_app_iff; auto. } }
             specialize_by auto.
             simpl in H.
             rewrite Hinout in H.
             specialize_by reflexivity.

             repeat (specialize (fun a b => H (conj a b)); specialize_by auto).
               (*
             specialize_by eauto with wf.
                   pose (LetIn ein Cst) as ein';
                   pose (LetIn ein Cst) as eout';
                   pose (LetIn ein Cst) as ebounds'.
             Focus 2.
             simpl.
             { cbv [LetIn.Let_In].
               intros.
               pose proof Hwf as Hwf'.
               eapply interpf_wff with (R:=@is_bounded_by') in Hwf';
                 [ | solve [ apply is_bounded_by_interp_op ] | solve [ auto ] ].
               unfold bound_is_good in Hgood.
               unfold bound_is_goodb in Hgood.
               break_match_hyps; try congruence.
               simpl in * |- .
               unfold is_bounded_by' in *.
               unfold bounds_to_base_type.
               unfold bounds_to_base_type'.
               unfold SmartCast.SmartCast_base.
               destruct_head' and.
               repeat break_innermost_match; simpl in *; try congruence.
               Focus 2.
               { unfold add in *.
                 unfold is_bounded_byb in *.
                 unfold t_map2 in *.
                 unfold add' in *.
                 unfold SmartBuildBounds in *.
                 break_match_hyps; inversion_option; subst; simpl in *; split_andb; congruence. }
               Unfocus.
               rewrite_hyp !*; simpl.
               unfold add in *.
               Locate wadd_def_ZToWord.
               rewrite wadd_def_ZToWord.
               Focus 2.
               { unfold t_map2, add', SmartBuildBounds, is_bounded_byb in *.
                 break_match_hyps; simpl in *; inversion_option; split_andb; subst; simpl in *.
                 Z.ltb_to_lt.
                 rewrite !wordToZ_ZToWord by repeat (t || misc_t_2 || inequality_t).
                 repeat (t || misc_t_2 || inequality_t). }
               Unfocus.
               { repeat (t || misc_t_2 || inequality_t || break_match_hyps).
                 all:destruct (interpf Syntax.interp_op ein) as [x y]; simpl in *; subst.
                 all:destruct (interpf Syntax.interp_op eout) as [x y]; simpl in *; subst.
                 { repeat rewrite !wordToZ_ZToWord; repeat (t || misc_t_2 || inequality_t || break_match_hyps). }
                 { repeat rewrite !wordToZ_ZToWord; repeat (t || misc_t_2 || inequality_t || break_match_hyps). } } }
             Unfocus.
             Print SmartBound.
             .
             simpl in *.
             cbv [LetIn.Let_In] in *.
             unfold SmartCast.SmartCast_base in *.
               t.
                 destruct (interpf Syntax.interp_op eout) as [x y]; simpl in *; subst.
                 destruct (interpf Syntax.interp_op ein) as [x y]; simpl in *.
                 destruct (Z_zerop upper1), (Z_zerop upper0); subst; simpl;
                   try assert (x = 0%Z) by omega;
                   try assert (y = 0%Z) by omega;
                   subst; simpl;
                     try rewrite Z.log2_up_eqn by omega;
                     rewrite <- ?Z.add_1_r, <- ?Z.sub_1_r;
                     autorewrite with zsimplify;
                     try (apply Z.log2_le_mono; omega).
                 SearchAbout Z.pred (-1 )%Z.
                 Focus 2.
                 SearchAbout Z.log2 Z.log2_up.
                 Focus 2.
                 { repeat (t || misc_t_2 || inequality_t). }
                 Unfocus.
                 Typeclasses eauto := debug.
                 Import Morphisms RelationClasses.
                 pose proof (_ : Proper (_ ==> Z.le --> _) Z.pow).
                 try rewrite <- Z.log2_up_le_full.
                 pose


                 Set Printing Coercions.
                 .
                 Focus 2.
                 { t.
                   .
               .
             SearchAbout FixedWordSizes.wadd.
             rewrite Heqb0.
             unfold is_bounded_byb.*)
    Admitted.
    Local Hint Resolve add_is_bounded_by_bound_op.
    Lemma sub_is_bounded_by_bound_op : is_bounded_by_bound_opT Sub.
    Proof. precutZ. Admitted.
    Local Hint Resolve sub_is_bounded_by_bound_op.
    Lemma mul_is_bounded_by_bound_op : is_bounded_by_bound_opT Mul.
    Proof. precutZ. Admitted.
    Local Hint Resolve mul_is_bounded_by_bound_op.
    Lemma shl_is_bounded_by_bound_op : is_bounded_by_bound_opT Shl.
    Proof. precutZ. Admitted.
    Local Hint Resolve shl_is_bounded_by_bound_op.
    Lemma shr_is_bounded_by_bound_op : is_bounded_by_bound_opT Shr.
    Proof. precutZ. Admitted.
    Local Hint Resolve shr_is_bounded_by_bound_op.
    Lemma land_is_bounded_by_bound_op : is_bounded_by_bound_opT Land.
    Proof. precutZ. Admitted.
    Local Hint Resolve land_is_bounded_by_bound_op.
    Lemma lor_is_bounded_by_bound_op : is_bounded_by_bound_opT Lor.
    Proof. precutZ. Admitted.
    Local Hint Resolve lor_is_bounded_by_bound_op.
    Lemma neg_is_bounded_by_bound_op int_size : is_bounded_by_bound_opT (fun T => Neg T int_size).
    Proof. precutZ.
           intros H G ein eout ebounds Hwf HG Hinout Hrgood Hgood;
             specialize (H G).
           Focus 2.
           { simpl. t.
    Admitted.
    Local Hint Resolve neg_is_bounded_by_bound_op.
    Lemma cmovne_is_bounded_by_bound_op : is_bounded_by_bound_opT Cmovne.
    Proof. precutZ. Admitted.
    Local Hint Resolve cmovne_is_bounded_by_bound_op.
    Lemma cmovle_is_bounded_by_bound_op : is_bounded_by_bound_opT Cmovle.
    Proof. precutZ. Admitted.
    Local Hint Resolve cmovle_is_bounded_by_bound_op.
    Lemma cast_is_bounded_by_bound_op T : is_bounded_by_bound_opT (Cast T).
    Proof. precutZ. Admitted.
    Local Hint Resolve cast_is_bounded_by_bound_op.

    Lemma is_bounded_by_bound_op
          G t tR (opc : op t tR) ein eout ebounds
          (Hwf : wff G ein ebounds)
          (HG : G_invariant_holds G)
          (Hinout : interpf Syntax.interp_op ein = interpf Syntax.interp_op eout)
          (Hrgood : bounds_are_recursively_good (@Bounds.interp_op) bound_is_good ebounds)
          (Hgood : bounds_are_good (@Bounds.interp_op _ _ opc (interpf (@Bounds.interp_op) ebounds)))
      : is_bounded_by
          (interpf Syntax.interp_op (@bound_op Syntax.interp_base_type _ _ _ _ opc opc eout (interpf (@Bounds.interp_op) ebounds)))
          (interpf (@Bounds.interp_op) (Op opc ebounds)).
    Proof.
      destruct opc; eauto.
      { (* const casse *) t. }
    Qed.


    Lemma add_interpf_bound_op : interpf_bound_opT Add.
    Proof. precutZ.
           intros H G ein eout ebounds Hwf HG Hinout Hrgood Hgood;
             specialize (H G). Admitted.
    Local Hint Resolve add_interpf_bound_op.
    Lemma sub_interpf_bound_op : interpf_bound_opT Sub.
    Proof. precutZ. Admitted.
    Local Hint Resolve sub_interpf_bound_op.
    Lemma mul_interpf_bound_op : interpf_bound_opT Mul.
    Proof. precutZ. Admitted.
    Local Hint Resolve mul_interpf_bound_op.
    Lemma shl_interpf_bound_op : interpf_bound_opT Shl.
    Proof. precutZ. Admitted.
    Local Hint Resolve shl_interpf_bound_op.
    Lemma shr_interpf_bound_op : interpf_bound_opT Shr.
    Proof. precutZ. Admitted.
    Local Hint Resolve shr_interpf_bound_op.
    Lemma land_interpf_bound_op : interpf_bound_opT Land.
    Proof. precutZ. Admitted.
    Local Hint Resolve land_interpf_bound_op.
    Lemma lor_interpf_bound_op : interpf_bound_opT Lor.
    Proof. precutZ. Admitted.
    Local Hint Resolve lor_interpf_bound_op.
    Lemma neg_interpf_bound_op int_size : interpf_bound_opT (fun T => Neg T int_size).
    Proof. precutZ.
           intros H G ein eout ebounds Hwf HG Hinout Hrgood Hgood;
             specialize (H G).
           Focus 2.
           { simpl. t.
    Admitted.
    Local Hint Resolve neg_interpf_bound_op.
    Lemma cmovne_interpf_bound_op : interpf_bound_opT Cmovne.
    Proof. precutZ. Admitted.
    Local Hint Resolve cmovne_interpf_bound_op.
    Lemma cmovle_interpf_bound_op : interpf_bound_opT Cmovle.
    Proof. precutZ. Admitted.
    Local Hint Resolve cmovle_interpf_bound_op.
    Lemma cast_interpf_bound_op T : interpf_bound_opT (Cast T).
    Proof. simpl; congruence. Qed.
    Local Hint Resolve cast_interpf_bound_op.

    Lemma interpf_bound_op
          G t tR (opc : op t tR) ein eout ebounds
          (Hwf : wff G ein ebounds)
          (HG : G_invariant_holds G)
          (Hinout : interpf Syntax.interp_op ein = interpf Syntax.interp_op eout)
          (Hrgood : bounds_are_recursively_good (@Bounds.interp_op) bound_is_good ebounds)
          (Hgood : bounds_are_good (@Bounds.interp_op _ _ opc (interpf (@Bounds.interp_op) ebounds)))
      : interpf Syntax.interp_op (@bound_op Syntax.interp_base_type t tR t tR opc opc eout (interpf (@Bounds.interp_op) ebounds))
        = interpf Syntax.interp_op (Op opc ein).
    Proof.
      destruct opc; eauto.
    Qed.
    End with_le_instances.
  End bounded_by_interp_op.

  Local Hint Resolve @is_bounded_by_interp_op @is_bounded_by_bound_op @interpf_bound_op.

  Definition MapBounds {t}
             (e : Expr base_type op t)
             (input_bounds : interp_flat_type Bounds.interp_base_type (domain t))
    : Expr base_type op _
    := @Boundify
         base_type op
         (@Bounds.interp_base_type) (@Bounds.interp_op)
         (fun _ => bounds_to_base_type)
         base_type_beq internal_base_type_dec_bl
         base_type_leb
         (@Castb)
         is_cast is_const
         genericize_op
         (fun _ t => Op (OpConst (ZToInterp 0)) TT)
         t e input_bounds.

  Lemma MapBounds_correct_and_bounded {t}
        (e : Expr base_type op t)
        (Hwf : Wf e)
        (input_bounds : interp_flat_type interp_base_type (domain t))
        (output_bounds := ComputeBounds e input_bounds)
        (e' := MapBounds e input_bounds)
        (Hgood : bounds_are_recursively_good
                   (@interp_op) bound_is_good
                   (invert_Abs (e interp_base_type) input_bounds))
    : forall x y,
      map_uncast_const input_bounds x = y
      -> is_bounded_by y input_bounds
      -> is_bounded_by (Interp (@Syntax.interp_op) e y) output_bounds
         /\ map_uncast_const _ (Interp (@Syntax.interp_op) e' x)
            = Interp (@Syntax.interp_op) e y.
  Proof.
    intros x y ? Hb; subst y output_bounds e'.
    unfold MapBounds, ComputeBounds.
    eapply InterpBoundifyAndRel; eauto with wf.
    { apply is_cast_correct. }
    { apply strip_cast_const. }
    { apply is_bounded_by_interp_op. }
    { apply is_bounded_by_bound_op. }
  Qed.

  Lemma MapBounds_correct_and_bounded_bool {t}
        (e : Expr base_type op t)
        (Hwf : Wf e)
        (input_bounds : interp_flat_type interp_base_type (domain t))
        (output_bounds := ComputeBounds e input_bounds)
        (e' := MapBounds e input_bounds)
        (Hgood : ((bounds_are_recursively_goodb
                     (@interp_op) bound_is_goodb
                     (invert_Abs (e interp_base_type) input_bounds)))%bool
                 = true)
    : forall x,
      is_bounded_by (map_uncast_const input_bounds x) input_bounds
      -> is_bounded_by (Interp (@Syntax.interp_op) e (map_uncast_const _ x)) output_bounds
         /\ map_uncast_const _ (Interp (@Syntax.interp_op) e' x)
            = Interp (@Syntax.interp_op) e (map_uncast_const _ x).
  Proof.
    intros; eapply MapBounds_correct_and_bounded; eauto.
    { apply bounds_are_recursively_good_iff_bool; assumption. }
  Qed.


  (*


  Local Notation new_flat_type (*: forall t, interp_flat_type interp_base_type2 t -> flat_type base_type_code1*)
    := (@SmartFlatTypeMap2 _ _ interp_base_type (fun t v => Tbase (bounds_to_base_type v))).
  Lemma new_flat_type_Pair {A B} (v : interp_flat_type _ A * interp_flat_type _ B)
    : @new_flat_type (Prod A B) v = Prod (new_flat_type (fst v)) (new_flat_type (snd v)).
  Proof. reflexivity. Qed.
  Local Ltac rewrite_new_flat_type_Pair :=
    match goal with
    | [ |- context[@new_flat_type (Prod ?A ?B) ?VVV] ]
      => progress change (@new_flat_type (Prod A B) VVV) with (Prod (@new_flat_type A (fst VVV)) (@new_flat_type B (snd VVV))) in *
    | [ H : context[@new_flat_type (Prod ?A ?B) ?VVV] |- _ ]
      => progress change (@new_flat_type (Prod A B) VVV) with (Prod (@new_flat_type A (fst VVV)) (@new_flat_type B (snd VVV))) in *
    end.
  Definition new_type {t}
    : forall (ve : interp_flat_type interp_base_type (domain t))
             (v : interp_type interp_base_type t),
      type base_type
    := fun ve v => Arrow (@new_flat_type (domain t) ve) (@new_flat_type (codomain t) (v ve)).
  Definition SmartBoundv {var t} (bounds : interp_flat_type Bounds.interp_base_type t) (e : interp_flat_type var t)
    : interp_flat_type (fun t => @exprf base_type op var (Tbase t)) (new_flat_type bounds)
    := SmartFlatTypeMap2Interp2 (f:=fun _ _ => Tbase _) (fun t b v => SmartCast_base (Var v)) bounds e.
  Definition map_cast_const {t} (bounds : interp_flat_type Bounds.interp_base_type t) (e : interp_flat_type Syntax.interp_base_type t)
    : interp_flat_type Syntax.interp_base_type (new_flat_type bounds)
    := SmartFlatTypeMap2Interp2 (f:=fun _ _ => Tbase _) (fun t b v => cast_const v) bounds e.
  Definition map_uncast_const {t} (bounds : interp_flat_type Bounds.interp_base_type t) (e : interp_flat_type Syntax.interp_base_type (new_flat_type bounds))
    : interp_flat_type Syntax.interp_base_type t
    := SmartFlatTypeMapUnInterp2 (f:=fun _ _ => Tbase _) (fun t b v => cast_const v) e.
  Definition SmartUnboundv {var t} {bounds : interp_flat_type Bounds.interp_base_type t}
             (e : interp_flat_type var (new_flat_type bounds))
    : interp_flat_type (fun t => @exprf base_type op var (Tbase t)) t
    := SmartFlatTypeMapUnInterp2 (f:=fun _ _ => Tbase _) (fun t b (v : var _) => SmartCast_base (Var v)) e.
  Definition SmartBound {t} (e : Expr base_type op t)
             (input_bounds : interp_flat_type Bounds.interp_base_type (domain t))
    : Expr base_type op (new_type input_bounds (Interp (@Bounds.interp_op) e))
    := fun var => Abs (fun x => LetIn
                                  (LetIn (SmartPairf (SmartUnboundv x))
                                         (invert_Abs (e var)))
                                  (fun v => SmartPairf (SmartBoundv _ v))).

  Lemma map_cast_const_Pair {A B} bounds e
    : @map_cast_const (Prod A B) bounds e
      = (map_cast_const (fst bounds) (fst e), map_cast_const (snd bounds) (snd e)).
  Proof. reflexivity. Qed.

  Lemma map_uncast_const_Pair {A B} bounds e
    : @map_uncast_const (Prod A B) bounds e
      = (map_uncast_const (fst bounds) (fst e), map_uncast_const (snd bounds) (snd e)).
  Proof. reflexivity. Qed.

  Lemma SmartUnboundv_Pair {var A B} bounds e
    : @SmartUnboundv var (Prod A B) bounds e
      = (SmartUnboundv (fst e), SmartUnboundv (snd e)).
  Proof. reflexivity. Qed.

  Lemma SmartBoundv_Pair {var A B} (bounds : interp_flat_type _ _ * interp_flat_type _ _)
        (e : interp_flat_type _ _ * interp_flat_type _ _)
    : @SmartBoundv var (Prod A B) bounds e
      = (SmartBoundv (t:=A) (fst bounds) (fst e), SmartBoundv (t:=B) (snd bounds) (snd e)).
  Proof. reflexivity. Qed.

  Local Hint Resolve List.in_or_app.

  Lemma wff_SmartUnboundv {var1 var2} t input_bounds
        (x : interp_flat_type var1 (new_flat_type (t:=t) input_bounds))
        (x' : interp_flat_type var2 (new_flat_type input_bounds))
    : wff (flatten_binding_list x x')
          (SmartPairf (SmartUnboundv x))
          (SmartPairf (SmartUnboundv x')).
  Proof.
    induction t; simpl in *;
      try rewrite_new_flat_type_Pair;
      rewrite ?SmartUnboundv_Pair, ?SmartPairf_Pair;
      try constructor;
      try solve [ eapply wff_in_impl_Proper; eauto ].
    { unfold SmartPairf, SmartUnboundv, SmartCast_base; simpl;
        break_match.
      { let H := match goal with H : _ = _ |- _ => H end in
        case H; repeat constructor. }
      { repeat constructor. } }
  Qed.

  Local Hint Resolve @wff_SmartUnboundv.

  Lemma wff_SmartBoundv {var1 var2} G t f x1 x2
        (Hwf : wff (op:=op) G (SmartVarf x1) (SmartVarf x2))
    : wff (var1:=var1) (var2:=var2) G
          (SmartPairf (SmartBoundv f x1))
          (SmartPairf (SmartBoundv (t:=t) f x2)).
  Proof.
    induction t; simpl in *;
      destruct_head' prod;
      rewrite ?SmartVarf_Pair in Hwf;
      rewrite ?SmartBoundv_Pair; simpl in *;
        try setoid_rewrite SmartPairf_Pair;
        inversion_wf;
        destruct_head' and;
        try constructor; eauto.
    { unfold SmartPairf, SmartBoundv, SmartCast_base, SmartFlatTypeMap2, SmartVarf in *; simpl in *.
      break_match; repeat (trivial || constructor). }
  Qed.

  Local Hint Resolve wff_SmartBoundv.

  Local Hint Resolve wff_SmartVarf.

  Lemma Wf_SmartBound {t} e input_bounds
        (Hwf : Wf e)
    : Wf (@SmartBound t e input_bounds).
  Proof.
    intros var1 var2; specialize (Hwf var1 var2).
    unfold SmartBound.
    destruct Hwf; constructor; intros; simpl.
    repeat constructor; eauto using wff_in_impl_Proper.
  Qed.

  (** We can squash [a -> b -> c] into [a -> c] if [min a b c = min a
      c], i.e., if the narrowest type we pass through in the original
      case is the same as the narrowest type we pass through in the
      new case. *)
  Definition squash_cast {var} (a b c : base_type) : @exprf base_type op var (Tbase a) -> @exprf base_type op var (Tbase c)
    := if base_type_beq (base_type_min b (base_type_min a c)) (base_type_min a c)
       then SmartCast_base
       else fun x => Op (Cast b c) (Op (Cast a b) x).
  Fixpoint maybe_push_cast {var t} (v : @exprf base_type op var t) : option (@exprf base_type op var t)
    := match v in exprf _ _ t return option (exprf _ _ t) with
       | Var _ _ as v'
         => Some v'
       | Op t1 tR opc args
         => match opc in op src dst return exprf _ _ src -> option (exprf _ _ dst) with
            | Cast b c
              => fun args
                 => match @maybe_push_cast _ _ args with
                    | Some (Op _ _ opc' args')
                      => match opc' in op src' dst' return exprf _ _ src' -> option (exprf _ _ (Tbase c)) with
                         | Cast a b
                           => fun args''
                              => Some (squash_cast a b c args'')
                         | OpConst _ v
                           => fun args''
                              => Some (SmartCast_base (Op (OpConst v) TT))
                         | _ => fun _ => None
                         end args'
                    | Some (Var _ v as v') => Some (SmartCast_base v')
                    | Some _ => None
                    | None => None
                    end
            | OpConst _ v
              => fun _ => Some (Op (OpConst v) TT)
            | _ => fun _ => None
            end args
       | Pair _ _ _ _
       | LetIn _ _ _ _
       | TT
         => None
       end.
  Definition push_cast {var t} : @exprf base_type op var t -> inline_directive (op:=op) (var:=var) t
    := match t with
       | Tbase _ => fun v => match maybe_push_cast v with
                             | Some e => inline e
                             | None => default_inline v
                             end
       | _ => default_inline
       end.

  (*Definition mapf_interpToZ_T (T : flat_type base_type) : flat_type base_type
    :=
*)
  Definition mapf_interpToZ {T} : interp_flat_type Syntax.interp_base_type T -> interp_flat_type (fun _ => Z) T
    := SmartVarfMap (fun _ => interpToZ).
  Definition mapf_interp_new_flat_typeToZ {T v} : interp_flat_type Syntax.interp_base_type (@new_flat_type T v) -> interp_flat_type (fun _ => Z) T
    := SmartFlatTypeMapUnInterp2 (f:=fun _ _ => Tbase _) (fun _ _ => interpToZ).

  Lemma mapf_interpToZ_Pair {A B} x
    : @mapf_interpToZ (Prod A B) x = (mapf_interpToZ (fst x), mapf_interpToZ (snd x)).
  Proof. reflexivity. Qed.
  Lemma mapf_interp_new_flat_typeToZ_Pair {A B} v e
    : @mapf_interp_new_flat_typeToZ (Prod A B) v e = (mapf_interp_new_flat_typeToZ (fst e), mapf_interp_new_flat_typeToZ (snd e)).
  Proof. reflexivity. Qed.

  (** TODO: move me *)

  Lemma interpf_maybe_push_cast t (e1 e2 : exprf base_type op t)
        (H : maybe_push_cast e1 = Some e2)
    : interpf Syntax.interp_op e1 = interpf Syntax.interp_op e2.
  Proof.
    revert dependent e2; induction e1; intro e2;
      try (preinvert_one_type e2; intros ? e2); destruct e2;
        try exact I;
        repeat match goal with
               | _ => intro
               | _ => reflexivity
               | [ H : forall e, Some _ = Some e -> _ |- _ ] => specialize (H _ eq_refl)
               | [ H : base_type_beq _ _ = true |- _ ] => apply internal_base_type_dec_bl in H
               | _ => progress subst
               | _ => progress inversion_option
               | _ => progress inversion_sigma
               | _ => progress inversion_prod
               | _ => progress inversion_expr
               | _ => progress simpl in *
               | _ => congruence
               | _ => progress break_match_hyps
               | _ => progress break_innermost_match_step
               | _ => progress invert_match_op
               | _ => progress invert_match_expr
               | _ => progress unfold SmartCast_base, squash_cast in *
               | _ => rewrite_hyp !*
               | _ => rewrite cast_const_id in *
               | _ => rewrite cast_const_idempotent by assumption
               end.
  Qed.

  Lemma interpf_push_cast t (e : exprf base_type op t)
    : interpf Syntax.interp_op (exprf_of_inline_directive (push_cast e)) = interpf Syntax.interp_op e.
  Proof.
    unfold push_cast;
      break_match; try reflexivity; simpl; [].
    symmetry; apply (@interpf_maybe_push_cast (Tbase _)); assumption.
  Qed.

  Local Hint Resolve interpf_push_cast.

  Local Hint Constructors wff.

  Local Ltac t_pair :=
    repeat first [ exact I
                 | intro
                 | progress subst
                 | progress destruct_head' False
                 | progress destruct_head' sig
                 | progress destruct_head' and
                 | progress inversion_option
                 | progress inversion_sigma
                 | progress inversion_prod
                 | progress break_match
                 | progress simpl in *
                 | progress inversion_wf ].

  Lemma wff_SmartCast_base {var1 var2} G A A' e1 e2
        (Hwf : wff G e1 e2)
    : wff G (@SmartCast_base var1 A A' e1) (@SmartCast_base var2 A A' e2).
  Proof.
    unfold SmartCast_base; break_match; auto.
  Qed.

  Local Hint Resolve @wff_SmartCast_base.

  Local Hint Extern 2 => progress simpl.

  Lemma wff_PairCast {var1 var2} G a b a' b'
        (e1 e2 : exprf base_type op (Tbase a * Tbase b))
        (Hwf : wff (var1:=var1) (var2:=var2) G e1 e2)
    : wff (t:=Prod (Tbase a') (Tbase b')) G (PairCast e1) (PairCast e2).
  Proof.
    apply wff_encode in Hwf; unfold wff_code in *;
      preinvert_one_type e1; intros ? e1; destruct e1; try exact I; t_pair;
        preinvert_one_type e2; intros ? e2; destruct e2; try exact I; t_pair;
          repeat constructor; eauto 6.
  Qed.

  Local Hint Resolve wff_PairCast.

  Lemma wff_QuadCast {var1 var2} G a b c d a' b' c' d'
        (e1 e2 : exprf base_type op (Tbase a * Tbase b * Tbase c * Tbase d))
        (Hwf : wff (var1:=var1) (var2:=var2) G e1 e2)
    : wff G (@QuadCast var1 a b c d a' b' c' d' e1) (QuadCast e2).
  Proof.
    apply wff_encode in Hwf; unfold wff_code in *;
      repeat match goal with
             | [ e : exprf _ _ (_ * _) |- _ ]
               => preinvert_one_type e; intros ? e; destruct e; try exact I; t_pair
             end;
      repeat constructor; eauto 10.
  Qed.

  Local Hint Resolve wff_QuadCast.

  Lemma wff_cast_bound_op {ovar1 ovar2} G src1 dst1 src2 dst2
        (opc1 : op src1 dst1) (opc2 : op src2 dst2)
        (e1 e2 : exprf base_type op src1)
        (args2 : interp_flat_type interp_base_type src2)
        (Hwf : wff (var1:=ovar1) (var2:=ovar2) G e1 e2)
    : wff G (cast_bound_op opc1 opc2 e1 args2) (cast_bound_op opc1 opc2 e2 args2).
  Proof.
    destruct opc1, opc2; simpl; auto;
      unfold SmartCast_op1, SmartCast_op2, SmartCast_op4, SmartCast_base; break_match; subst;
        trivial;
        try constructor; trivial; eauto.
  Qed.

  Local Hint Resolve wff_cast_bound_op : wf.

  Local Hint Resolve Wf_Linearize Wf_SmartBound Wf_MapInterpCast : wf.

  Lemma interpf_SmartCast_base {A A'} e
    : interpf (@Syntax.interp_op) (@SmartCast_base _ A A' e) = cast_const (interpf (@Syntax.interp_op) e).
  Proof.
    unfold SmartCast_base; break_match; rewrite ?cast_const_id; reflexivity.
  Qed.

  Lemma interpf_PairCast {A B A' B'} e
    : interpf (@Syntax.interp_op) (@PairCast _ A B A' B' e)
      = let ev := interpf (@Syntax.interp_op) e in
        (cast_const (fst ev), cast_const (snd ev)).
  Proof.
    invert_expr; break_innermost_match; try exact I; simpl;
      cbv [LetIn.Let_In];
      rewrite ?interpf_SmartCast_base;
      reflexivity.
  Qed.

  Lemma interpf_QuadCast {A B C D A' B' C' D'} e
    : interpf (@Syntax.interp_op) (@QuadCast _ A B C D A' B' C' D' e)
      = let ev := interpf (@Syntax.interp_op) e in
        (cast_const (fst (fst (fst ev))),
         cast_const (snd (fst (fst ev))),
         cast_const (snd (fst ev)),
         cast_const (snd ev)).
  Proof.
    repeat first [ exact I
                 | reflexivity
                 | rewrite !interpf_SmartCast_base
                 | progress cbv [LetIn.Let_In]
                 | progress simpl
                 | progress break_innermost_match
                 | progress invert_expr ].
  Qed.

  Lemma interpf_PairCast_uniform {A A'} e
    : interpf (@Syntax.interp_op) (@PairCast _ A A A' A' e)
      = SmartVarfMap (fun t => cast_const) (interpf (@Syntax.interp_op) e).
  Proof. rewrite interpf_PairCast; reflexivity. Qed.

  Lemma interpf_QuadCast_uniform {A A'} e
    : interpf (@Syntax.interp_op) (@QuadCast _ A A A A A' A' A' A' e)
      = SmartVarfMap (fun t => cast_const) (interpf (@Syntax.interp_op) e).
  Proof. rewrite interpf_QuadCast; reflexivity. Qed.

  Local Ltac rewrite_in_all lem :=
    match goal with
    | _ => rewrite lem
    | [ H : _ |- _ ] => rewrite lem in H
    end.

  Local Ltac t_interpf_step :=
    first [ reflexivity
          | assumption
          | progress destruct_head_hnf' unit
          | progress destruct_head_hnf' and
          | progress rewrite_new_flat_type_Pair
          | rewrite_in_all SmartBoundv_Pair
          | rewrite_in_all SmartUnboundv_Pair
          | rewrite_in_all SmartPairf_Pair
          | rewrite_in_all interpf_SmartCast_base
          | rewrite_in_all map_cast_const_Pair
          | rewrite_in_all map_uncast_const_Pair
          | rewrite_in_all mapf_interpToZ_Pair
          | rewrite_in_all mapf_interp_new_flat_typeToZ_Pair
          | rewrite Z2Nat.id by auto with zarith
          | progress split_andb
          | rewrite_hyp !*
          | progress (simpl @fst; simpl @snd)
          | progress break_match_hyp
          | progress subst
          | progress break_innermost_match_step
          | progress Z.ltb_to_lt
          | rewrite_in_all Z.pow_Zpow
          | omega ].

  Lemma interpf_SmartPairf_SmartBoundv {t} bounds e
    : interpf (@Syntax.interp_op) (SmartPairf (@SmartBoundv (@Syntax.interp_base_type) t bounds e))
      = map_cast_const bounds e.
  Proof.
    induction t;
      repeat first [ t_interpf_step
                   | progress simpl in *
                   | progress unfold SmartPairf, SmartBoundv, SmartFlatTypeMap2 ].
  Qed.

  Lemma interpf_SmartPairf_SmartUnboundv {t} bounds e
    : interpf (@Syntax.interp_op) (SmartPairf (@SmartUnboundv (@Syntax.interp_base_type) t bounds e))
      = map_uncast_const bounds e.
  Proof.
    induction t;
      repeat first [ t_interpf_step
                   | progress simpl in *
                   | progress unfold SmartPairf, SmartUnboundv, SmartFlatTypeMap2 ].
  Qed.

  Local Arguments Z.add !_ !_.
  Local Existing Instances Z.add_le_Proper Z.sub_le_eq_Proper Z.log2_up_le_Proper Z.pow_Zpos_le_Proper.
  Lemma mapf_interp_new_flat_typeToZ__map_cast_const {t} bounds e
        (Hbounded : is_bounded_by e bounds)
    : mapf_interp_new_flat_typeToZ (@map_cast_const t bounds e)
      = mapf_interpToZ e.
  Proof.
    induction t;
      repeat first [ t_interpf_step
                   | progress simpl in *
                   | progress unfold map_cast_const, mapf_interp_new_flat_typeToZ
                   | progress unfold is_bounded_by in *
                   | progress unfold mapf_interpToZ, SmartVarfMap in *
                   | progress unfold cast_const, bounds_to_base_type'
                   | rewrite wordToZ_ZToWord
                   | split; [ reflexivity | ]
                   | match goal with
                     | [ |- (?x < ?y)%Z ]
                       => cut (x <= y - 1)%Z; [ omega | ]
                     end
                   | rewrite <- !Z.log2_up_le_full
                   | progress unfold is_bounded_by', is_bounded_byb in * ].
  Qed.


  Lemma InterpSmartBound t e input_bounds
        (Hwf : Wf e)
    : forall (x : interp_flat_type Syntax.interp_base_type (new_flat_type (t:=domain t) input_bounds)),
      is_bounded_by (map_uncast_const input_bounds x) input_bounds
      -> mapf_interp_new_flat_typeToZ (Interp (@Syntax.interp_op) (SmartBound e input_bounds) x)
         = mapf_interpToZ (Interp (@Syntax.interp_op) e (map_uncast_const input_bounds x)).
  Proof.
    unfold SmartBound, Interp; simpl.
    cbv [LetIn.Let_In]; intros x H.
    rewrite interpf_SmartPairf_SmartBoundv, interpf_SmartPairf_SmartUnboundv, interpf_invert_Abs, mapf_interp_new_flat_typeToZ__map_cast_const; [ reflexivity | ].
    fold (@Interp _ _ _ (@interp_op) _ e).
    fold (@Interp _ _ _ (@Syntax.interp_op) _ e).
    apply InterpWf; [ | assumption.. ].
    intros src dst op sv1 sv2.
    fold (is_bounded_by sv1 sv2).
    fold (is_bounded_by (Syntax.interp_op src dst op sv1) (interp_op op sv2)).
    apply is_bounded_by_interp_op.
  Qed.

  Lemma interpf_SmartCast_op1 {T1 T2} (opc : forall t, op (Tbase t) (Tbase t)) args1 args2
        (HopcZ : forall T2 x xb zb,
            is_bounded_by (T:=Tbase TZ) x (Some xb)
            -> interp_op (opc T2) (Some xb) = Some zb
            -> FixedWordSizes.wordToZ (Syntax.interp_op _ _ (opc (TWord (Z.to_nat (Z.log2_up (Z.log2_up (Z.max (1 + upper xb) (1 + upper zb))))))) (FixedWordSizes.ZToWord x))
               = Syntax.interp_op _ _ (opc TZ) x)
        (Hb : is_bounded_by (interpf (@Syntax.interp_op) args1) args2)
    : interpf (@Syntax.interp_op) (@SmartCast_op1 _ T1 T2 opc args1 args2)
      = cast_const (Syntax.interp_op _ _ (opc TZ) (SmartVarfMap (fun t => @cast_const t TZ) (interpf (@Syntax.interp_op) args1))).
  Proof.
    unfold SmartCast_op1.
    unfold is_bounded_by, interp_flat_type_rel_pointwise, interp_flat_type_rel_pointwise_gen_Prop, is_bounded_by', is_bounded_byb in *.
    rewrite interpf_SmartCast_base; simpl.
    repeat unfold bounds3_to_base_type, bounds2_to_base_type, bounds_to_base_type, bounds_to_base_type', cast_const, ZToInterp, interpToZ; simpl.
    unfold base_type_max.
    unfold SmartVarfMap; simpl.
    unfold bit_width_of_base_type in *.
    rewrite interpf_SmartCast_base.
    repeat (break_innermost_match_step; simpl; try reflexivity);
      destruct_head' and;
      split_andb;
      generalize dependent (interpf Syntax.interp_op args1); clear args1; intros;
        simpl in *;
        rewrite <- !Z2Nat.inj_max, !Z.max_log2_up;
        erewrite HopcZ by (rewrite_hyp !*; reflexivity);
        reflexivity.
  Qed.

  Lemma interpf_SmartCast_op2 {T1 T2} (opc : forall t, op (Tbase t * Tbase t) (Tbase t)) args1 args2
        (HopcZ : forall T2 x y xb yb zb,
            is_bounded_by (T:=Prod (Tbase TZ) (Tbase TZ)) (x, y)%core (Some xb, Some yb)%core
            -> interp_op (opc T2) (Some xb, Some yb) = Some zb
            -> FixedWordSizes.wordToZ (Syntax.interp_op _ _ (opc (TWord (Z.to_nat (Z.log2_up (Z.log2_up (Z.max (Z.max (1 + upper xb) (1 + upper yb)) (1 + upper zb))))))) (FixedWordSizes.ZToWord x, FixedWordSizes.ZToWord y))
               = Syntax.interp_op _ _ (opc TZ) (x, y))
        (Hb : is_bounded_by (interpf (@Syntax.interp_op) args1) args2)
    : interpf (@Syntax.interp_op) (@SmartCast_op2 _ T1 T2 opc args1 args2)
      = cast_const (Syntax.interp_op _ _ (opc TZ) (SmartVarfMap (fun t => @cast_const t TZ) (interpf (@Syntax.interp_op) args1))).
  Proof.
    unfold SmartCast_op2.
    unfold is_bounded_by, interp_flat_type_rel_pointwise, interp_flat_type_rel_pointwise_gen_Prop, is_bounded_by', is_bounded_byb in *.
    rewrite interpf_SmartCast_base; simpl.
    rewrite interpf_PairCast_uniform.
    destruct_head_hnf prod.
    repeat unfold bounds3_to_base_type, bounds2_to_base_type, bounds_to_base_type, bounds_to_base_type', cast_const, ZToInterp, interpToZ; simpl.
    unfold base_type_max.
    unfold SmartVarfMap; simpl.
    unfold bit_width_of_base_type in *.
    repeat (break_innermost_match_step; simpl; try reflexivity);
      destruct_head' and;
      split_andb;
      generalize dependent (interpf Syntax.interp_op args1); clear args1; intros; destruct_head_hnf prod;
        rewrite <- !Z2Nat.inj_max, !Z.max_log2_up;
        erewrite HopcZ by (eassumption || rewrite_hyp !*; auto);
        reflexivity.
  Qed.

  Lemma interpf_SmartCast_op4 {T1 T2} (opc : forall t, op (Tbase t * Tbase t * Tbase t * Tbase t) (Tbase t)) args1 args2
        (HopcZ : forall T2 x y z w xb yb zb wb ob,
            is_bounded_by (T:=Prod (Prod (Prod (Tbase TZ) (Tbase TZ)) (Tbase TZ)) (Tbase TZ))
                          (x, y, z, w)%core (Some xb, Some yb, Some zb, Some wb)%core
            -> interp_op (opc T2) (Some xb, Some yb, Some zb, Some wb) = Some ob
            -> FixedWordSizes.wordToZ (Syntax.interp_op _ _ (opc (TWord (Z.to_nat (Z.log2_up (Z.log2_up (Z.max (Z.max (Z.max (1 + upper xb) (1 + upper yb)) (Z.max (1 + upper zb) (1 + upper wb))) (1 + upper ob)))))))
                                                        (FixedWordSizes.ZToWord x, FixedWordSizes.ZToWord y, FixedWordSizes.ZToWord z, FixedWordSizes.ZToWord w))
               = Syntax.interp_op _ _ (opc TZ) (x, y, z, w))
        (Hb : is_bounded_by (interpf (@Syntax.interp_op) args1) args2)
    : interpf (@Syntax.interp_op) (@SmartCast_op4 _ T1 T2 opc args1 args2)
      = cast_const (Syntax.interp_op _ _ (opc TZ) (SmartVarfMap (fun t => @cast_const t TZ) (interpf (@Syntax.interp_op) args1))).
  Proof.
    unfold SmartCast_op4.
    unfold is_bounded_by, interp_flat_type_rel_pointwise, interp_flat_type_rel_pointwise_gen_Prop, is_bounded_by', is_bounded_byb in *.
    rewrite interpf_SmartCast_base; simpl.
    rewrite interpf_QuadCast_uniform.
    destruct_head_hnf prod.
    repeat unfold bounds5_to_base_type, bounds4_to_base_type, bounds3_to_base_type, bounds2_to_base_type, bounds_to_base_type, bounds_to_base_type', cast_const, ZToInterp, interpToZ; simpl.
    unfold base_type_max.
    unfold SmartVarfMap; simpl.
    unfold bit_width_of_base_type in *.
    repeat (break_innermost_match_step; simpl; try reflexivity);
      destruct_head' and;
      split_andb;
      generalize dependent (interpf Syntax.interp_op args1); clear args1; intros; destruct_head_hnf prod;
        rewrite <- !Z2Nat.inj_max, !Z.max_log2_up;
        erewrite HopcZ by (eassumption || rewrite_hyp !*; auto);
        reflexivity.
  Qed.

    Lemma interpf_cast_bound_op G t0 tR (opc : op t0 tR)
        (ein eout ebounds : exprf base_type op t0)
        (HG : forall (t : base_type) (x : Syntax.interp_base_type t) (x' : interp_base_type t),
            List.In (existT _ t (x, x')) G
            -> is_bounded_by' x x')
        (Hwf : wff G ein ebounds)
        (He : interpf Syntax.interp_op ein = interpf Syntax.interp_op eout)
        (Hbounds_are_good : bounds_are_good (interpf (@interp_op) (Op opc ebounds)))
    : interpf Syntax.interp_op (cast_bound_op opc opc eout (interpf (@interp_op) ebounds))
      = interpf Syntax.interp_op (Op opc ein).
  Proof.
    assert (Hb : is_bounded_by (interpf Syntax.interp_op (Op opc ein)) (interpf (@interp_op) (Op opc ebounds)))
      by (eapply interpf_wff; eauto; apply is_bounded_by_interp_op).
    assert (Hb0 : is_bounded_by (interpf Syntax.interp_op ein) (interpf (@interp_op) ebounds))
      by (eapply interpf_wff; eauto; apply is_bounded_by_interp_op).
    destruct opc;
      repeat first [ intro
                   | reflexivity
                   | progress subst
                   | progress destruct_head' and
                   | solve [ rewrite_hyp <- ?*; eapply interpf_wff; [ .. | eassumption ]; eauto;
                             apply is_bounded_by_interp_op
                           | inversion_wf; eauto ]
                   | rewrite interpf_SmartCast_base
                   | rewrite interpf_SmartCast_op1
                   | rewrite interpf_SmartCast_op2
                   | rewrite interpf_SmartCast_op4
                   | rewrite_hyp !*
                   | progress simpl in *
                   | progress break_innermost_match ].
    all:unfold is_bounded_by', is_bounded_byb in *.
    all:simpl in *.
    { repeat first [ progress unfold add, add' in *
                   | progress unfold t_map2, SmartBuildBounds, bound_is_good, bound_is_goodb in *
                   | progress subst
                   | progress inversion_option
                   | progress split_andb
                   | progress break_match_hyps
                   | progress Z.ltb_to_lt
                   | progress simpl in *
                   | progress rewrite_hyp <- ?*
                   | match goal with
                     | [ H : context[andb _ _ = false] |- _ ] => rewrite Bool.andb_false_iff in H
                     end
                   | progress destruct_head' or
                   | exfalso; omega
                   | congruence ].
      { Local Ltac def_ZToWord_t :=
          first [ eapply Z.le_lt_trans; [ apply Z.log2_le_mono | eassumption ]; omega ].
        rewrite wadd_def_ZToWord by def_ZToWord_t.
        reflexivity. } }
    { repeat first [ progress unfold add, add' in *
                   | progress unfold t_map2, SmartBuildBounds, bound_is_good, bound_is_goodb, bit_width_of_base_type in *
                   | progress subst
                   | progress inversion_option
                   | progress split_andb
                   | progress break_match_hyps
                   | progress Z.ltb_to_lt
                   | progress simpl in *
                   | progress rewrite_hyp <- ?*
                   | match goal with
                     | [ H : context[andb _ _ = false] |- _ ] => rewrite Bool.andb_false_iff in H
                     end
                   | progress destruct_head' or
                   | exfalso; omega
                   | congruence ].
      { rewrite wadd_def_ZToWord;
          repeat rewrite !wordToZ_ZToWord.
        reflexivity.
        all:try split; try omega.
        all:rewrite ?Z.pow_Zpow, ?Z2Nat.id, ?Nat2Z.inj_succ, ?Nat2Z.inj_0, <- ?Z.one_succ, <- ?Z.two_succ.
        all:auto using Z.log2_up_nonneg.
        all: repeat apply Z.max_case_strong; intros.
        all: try (eapply Z.lt_le_trans; [ | rewrite <- !Z.log2_up_le_full_max; reflexivity ]).
        all: repeat apply Z.max_case_strong; intros.
        all: try (eapply Z.lt_le_trans; [ | rewrite <- !Z.log2_up_le_full_max; reflexivity ]).
        all: repeat apply Z.max_case_strong; intros.
        all: try omega.
        all: change (2^1)%Z with 2%Z in *.
        all: try omega.
        all:repeat match goal with
                   | [ H : (Z.log2_up _ <= 1)%Z |- _ ] => apply Z.log2_up_le_1 in H
                   | [ H : (1 <= Z.log2_up _)%Z |- _ ] => apply Z.log2_up_1_le in H
                   end.
        all: try omega.
        all: rewrite ?Z.log2_up_eqn by omega.
        all: try apply Zle_lt_succ.
        all: try apply Z.log2_le_mono.
        all: try omega.
        Local Open Scope Z_scope.
        all: repeat match goal with
                    | [ H : 1 + ?x <= 2 |- _ ] => assert (x <= 1) by omega; clear H
                    | [ H : 1 + ?x <= 1 |- _ ] => assert (x <= 0) by omega; clear H
                    | [ H : (?x <= 1)%Z |- _ ]
                      => is_var x;
                           assert (0 <= x <= 1) by omega;
                           assert (x = 0 \/ x = 1) by omega;
                           destruct_head' or; subst
                    | [ H : ?x + ?y <= 1 |- _ ]
                      => is_var x; is_var y;
                           assert (0 <= x + y <= 1) by omega;
                           assert ((x = 0 /\ y = 0) \/ (x = 0 /\ y = 1) \/ (x = 1 /\ y = 0)) by omega;
                           destruct_head' or; destruct_head' and; subst
                    | [ H : ?x <= 0 |- _ ]
                      => is_var x;
                           assert (x = 0) by omega;
                           destruct_head' or; subst
                    | [ H : ?x <= ?x |- _ ] => clear H
                    | [ H : ?a <= ?b, H' : ?a <= ?b |- _ ] => clear H'
                    | [ H : 0 <= 1 |- _ ] => clear H
                    | _ => progress simpl in *
                    | [ H : 0 <= 0 <= 1 |- _ ] => clear H
                    | [ H : context[0 + _] |- _ ] => rewrite Z.add_0_l in H
                    | [ H : 1 + ?x <= 1 + ?y |- _ ] => assert (x <= y) by omega; clear H
                    | [ H : ?x <= ?x + ?y |- _ ] => assert (0 <= y) by omega; clear H
                    | _ => omega
                    end. }
      { rewrite wadd_def_ZToWord;
          repeat rewrite !wordToZ_ZToWord.
        reflexivity.
        all:try split; try omega.
        all:rewrite ?Z.pow_Zpow, ?Z2Nat.id, ?Nat2Z.inj_succ, ?Nat2Z.inj_0, <- ?Z.one_succ, <- ?Z.two_succ.
        all:auto using Z.log2_up_nonneg.
        all: repeat apply Z.max_case_strong; intros.
        all: try (eapply Z.lt_le_trans; [ | rewrite <- !Z.log2_up_le_full_max; reflexivity ]).
        all: repeat apply Z.max_case_strong; intros.
        all: try (eapply Z.lt_le_trans; [ | rewrite <- !Z.log2_up_le_full_max; reflexivity ]).
        all: repeat apply Z.max_case_strong; intros.
        all: try omega.
        all: change (2^1) with 2 in *.
        all: try omega.
        all:repeat match goal with
                   | [ H : Z.log2_up _ <= 1 |- _ ] => apply Z.log2_up_le_1 in H
                   | [ H : 1 <= Z.log2_up _ |- _ ] => apply Z.log2_up_1_le in H
                   end.
        all: try omega.
        all: rewrite ?Z.log2_up_eqn by omega.
        all: try apply Zle_lt_succ.
        all: try apply Z.log2_le_mono.
        all: try omega.
        all: repeat match goal with
                    | [ H : 1 + ?x <= 2 |- _ ] => assert (x <= 1) by omega; clear H
                    | [ H : 1 + ?x <= 1 |- _ ] => assert (x <= 0) by omega; clear H
                    | [ H : ?x <= 1 |- _ ]
                      => is_var x;
                           assert (0 <= x <= 1) by omega;
                           assert (x = 0 \/ x = 1) by omega;
                           destruct_head' or; subst
                    | [ H : ?x + ?y <= 1 |- _ ]
                      => is_var x; is_var y;
                           assert (0 <= x + y <= 1) by omega;
                           assert ((x = 0 /\ y = 0) \/ (x = 0 /\ y = 1) \/ (x = 1 /\ y = 0)) by omega;
                           destruct_head' or; destruct_head' and; subst
                    | [ H : ?x <= 0 |- _ ]
                      => is_var x;
                           assert (x = 0) by omega;
                           destruct_head' or; subst
                    | [ H : ?x <= ?x |- _ ] => clear H
                    | [ H : ?a <= ?b, H' : ?a <= ?b |- _ ] => clear H'
                    | [ H : 0 <= 1 |- _ ] => clear H
                    | _ => progress simpl in *
                    | [ H : 0 <= 0 <= 1 |- _ ] => clear H
                    | [ H : context[0 + _] |- _ ] => rewrite Z.add_0_l in H
                    | [ H : 1 + ?x <= 1 + ?y |- _ ] => assert (x <= y) by omega; clear H
                    | [ H : ?x <= ?x + ?y |- _ ] => assert (0 <= y) by omega; clear H
                    | _ => omega
                    end. }
      { rewrite wadd_def_ZToWord;
          repeat rewrite !wordToZ_ZToWord.
        reflexivity.
        all:try split; try omega.
        all:rewrite ?Z.pow_Zpow, ?Z2Nat.id, ?Nat2Z.inj_succ, ?Nat2Z.inj_0, <- ?Z.one_succ, <- ?Z.two_succ.
        all:auto using Z.log2_up_nonneg.
        all: repeat apply Z.max_case_strong; intros.
        all: try (eapply Z.lt_le_trans; [ | rewrite <- !Z.log2_up_le_full_max; reflexivity ]).
        all: repeat apply Z.max_case_strong; intros.
        all: try (eapply Z.lt_le_trans; [ | rewrite <- !Z.log2_up_le_full_max; reflexivity ]).
        all: repeat apply Z.max_case_strong; intros.
        all: try omega.
        all: change (2^1) with 2 in *.
        all: try omega.
        all:repeat match goal with
                   | [ H : Z.log2_up _ <= 1 |- _ ] => apply Z.log2_up_le_1 in H
                   | [ H : 1 <= Z.log2_up _ |- _ ] => apply Z.log2_up_1_le in H
                   end.
        all: try omega.
        all: rewrite ?Z.log2_up_eqn by omega.
        all: try apply Zle_lt_succ.
        all: try apply Z.log2_le_mono.
        all: try omega.
        all: repeat match goal with
                    | [ H : 1 + ?x <= 2 |- _ ] => assert (x <= 1) by omega; clear H
                    | [ H : 1 + ?x <= 1 |- _ ] => assert (x <= 0) by omega; clear H
                    | [ H : ?x <= 1 |- _ ]
                      => is_var x;
                           assert (0 <= x <= 1) by omega;
                           assert (x = 0 \/ x = 1) by omega;
                           destruct_head' or; subst
                    | [ H : ?x + ?y <= 1 |- _ ]
                      => is_var x; is_var y;
                           assert (0 <= x + y <= 1) by omega;
                           assert ((x = 0 /\ y = 0) \/ (x = 0 /\ y = 1) \/ (x = 1 /\ y = 0)) by omega;
                           destruct_head' or; destruct_head' and; subst
                    | [ H : ?x <= 0 |- _ ]
                      => is_var x;
                           assert (x = 0) by omega;
                           destruct_head' or; subst
                    | [ H : ?x <= ?x |- _ ] => clear H
                    | [ H : ?a <= ?b, H' : ?a <= ?b |- _ ] => clear H'
                    | [ H : 0 <= 1 |- _ ] => clear H
                    | _ => progress simpl in *
                    | [ H : 0 <= 0 <= 1 |- _ ] => clear H
                    | [ H : context[0 + _] |- _ ] => rewrite Z.add_0_l in H
                    | [ H : 1 + ?x <= 1 + ?y |- _ ] => assert (x <= y) by omega; clear H
                    | [ H : ?x <= ?x + ?y |- _ ] => assert (0 <= y) by omega; clear H
                    | _ => omega
                    end. }
      { rewrite wadd_def_ZToWord;
          repeat rewrite !wordToZ_ZToWord.
        reflexivity.
        all:try split; try omega.
        all:rewrite ?Z.pow_Zpow, ?Z2Nat.id, ?Nat2Z.inj_succ, ?Nat2Z.inj_0, <- ?Z.one_succ, <- ?Z.two_succ.
        all:auto using Z.log2_up_nonneg.
        all: repeat apply Z.max_case_strong; intros.
        all: try (eapply Z.lt_le_trans; [ | rewrite <- !Z.log2_up_le_full_max; reflexivity ]).
        all: repeat apply Z.max_case_strong; intros.
        all: try (eapply Z.lt_le_trans; [ | rewrite <- !Z.log2_up_le_full_max; reflexivity ]).
        all: repeat apply Z.max_case_strong; intros.
        all: try omega.
        all: change (2^1) with 2 in *.
        all: try omega.
        all:repeat match goal with
                   | [ H : Z.log2_up _ <= 1 |- _ ] => apply Z.log2_up_le_1 in H
                   | [ H : 1 <= Z.log2_up _ |- _ ] => apply Z.log2_up_1_le in H
                   end.
        all: try omega.
        all: rewrite ?Z.log2_up_eqn by omega.
        all: try apply Zle_lt_succ.
        all: try apply Z.log2_le_mono.
        all: try omega.
        all: repeat match goal with
                    | [ H : 1 + ?x <= 2 |- _ ] => assert (x <= 1) by omega; clear H
                    | [ H : 1 + ?x <= 1 |- _ ] => assert (x <= 0) by omega; clear H
                    | [ H : ?x <= 1 |- _ ]
                      => is_var x;
                           assert (0 <= x <= 1) by omega;
                           assert (x = 0 \/ x = 1) by omega;
                           destruct_head' or; subst
                    | [ H : ?x + ?y <= 1 |- _ ]
                      => is_var x; is_var y;
                           assert (0 <= x + y <= 1) by omega;
                           assert ((x = 0 /\ y = 0) \/ (x = 0 /\ y = 1) \/ (x = 1 /\ y = 0)) by omega;
                           destruct_head' or; destruct_head' and; subst
                    | [ H : ?x <= 0 |- _ ]
                      => is_var x;
                           assert (x = 0) by omega;
                           destruct_head' or; subst
                    | [ H : ?x <= ?x |- _ ] => clear H
                    | [ H : ?a <= ?b, H' : ?a <= ?b |- _ ] => clear H'
                    | [ H : 0 <= 1 |- _ ] => clear H
                    | _ => progress simpl in *
                    | [ H : 0 <= 0 <= 1 |- _ ] => clear H
                    | [ H : context[0 + _] |- _ ] => rewrite Z.add_0_l in H
                    | [ H : 1 + ?x <= 1 + ?y |- _ ] => assert (x <= y) by omega; clear H
                    | [ H : ?x <= ?x + ?y |- _ ] => assert (0 <= y) by omega; clear H
                    | _ => omega
                    end. } }
  Admitted.

  Lemma is_bounded_by_cast_bound_op G t0 tR (opc : op t0 tR)
        (ein eout ebounds : exprf base_type op t0)
        (HG : forall (t : base_type) (x : Syntax.interp_base_type t) (x' : interp_base_type t),
            List.In (existT _ t (x, x')) G
            -> is_bounded_by' x x')
        (Hwf : wff G ein ebounds)
        (He : interpf Syntax.interp_op ein = interpf Syntax.interp_op eout)
        (Hbounds_are_good : bounds_are_good (interpf (@interp_op) (Op opc ebounds)))
    : is_bounded_by
        (interpf Syntax.interp_op (cast_bound_op opc opc eout (interpf (@interp_op) ebounds)))
        (interpf (@interp_op) (Op opc ebounds)).
  Proof.
    erewrite interpf_cast_bound_op by eassumption.
    simpl; apply is_bounded_by_interp_op.
    eapply interpf_wff; eauto; apply is_bounded_by_interp_op.
  Qed.

  Lemma MapBounds_correct_and_bounded {t}
        (e : Expr base_type op t)
        (Hwf : Wf e)
        (input_bounds : interp_flat_type interp_base_type (domain t))
        (output_bounds := ComputeBounds e input_bounds)
        (e' := MapBounds e input_bounds)
        (Hgood : bounds_are_recursively_good
                   (@interp_op) bound_is_good
                   (invert_Abs (e interp_base_type) input_bounds))
    : forall x y,
      map_uncast_const input_bounds x = y
      -> is_bounded_by y input_bounds
      -> is_bounded_by (Interp (@Syntax.interp_op) e (map_uncast_const _ x)) output_bounds
         /\ mapf_interp_new_flat_typeToZ (Interp (@Syntax.interp_op) e' x)
            = mapf_interpToZ (Interp (@Syntax.interp_op) e y).
  Proof.
    intros x y ? Hb; subst y output_bounds e'.
    unfold MapBounds, ComputeBounds.
    rewrite InterpExprEta.
    rewrite Interp_InlineConstGen by auto with wf.
    rewrite Interp_Linearize.
    rewrite InterpSmartBound by auto with wf.
    erewrite InterpMapInterpCast with (R':=@is_bounded_by')
      by solve [ eauto with wf
               | intros; eapply is_bounded_by_cast_bound_op; eauto
               | intros; eapply interpf_cast_bound_op; eauto ].
    split; [ | reflexivity ].
    eapply InterpWf; eauto; apply is_bounded_by_interp_op.
  Qed.*)


(*
  Definition is_bounded_and_correct {T1 T2 TB}
             (interpreted_val : interp_flat_type Syntax.interp_base_type T1)
             (orig_val : interp_flat_type Syntax.interp_base_type T2)
             (bounds : interp_flat_type interp_base_type TB)
    : Prop
    := mapf_interpToZ interpreted_val = orig_val

  (((Tuple.map (n:=k) fe25519WToZ irop = op)
       /\ HList.hlistP (fun v => is_bounded v = true) (Tuple.map (n:=k) fe25519WToZ irop))%type)*)
End Bounds.
