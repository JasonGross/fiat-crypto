Require Import Crypto.Compilers.Named.PositiveContext.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.InterpretToPHOASInterp.
Require Import Crypto.Compilers.Named.CompileWf.
Require Import Crypto.Compilers.Named.CompileInterp.
Require Import Crypto.Compilers.Named.WfFromUnit.
Require Import Crypto.Compilers.Named.DeadCodeEliminationInterp.
Require Import Crypto.Compilers.Named.WfInterp.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.RewriteAddToAdc.
Require Import Crypto.Compilers.Z.Named.RewriteAddToAdcInterp.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Bool.

Section language.
  Local Notation PContext var := (PositiveContext _ var _ internal_base_type_dec_bl).

  Lemma InterpRewriteAdc
        {interp_base_type}
        {interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst}
        {t} (e : Expr base_type op t) (Hwf : Wf e)
  : forall x, Interp interp_op (RewriteAdc e) x = Interp interp_op e x.
  Proof.
    intro x; unfold RewriteAdc, option_map; break_innermost_match; try reflexivity;
      match goal with |- ?x = ?y => cut (Some x = Some y); [ congruence | ] end;
      (etransitivity; [ symmetry; eapply @Interp_InterpToPHOAS | ]); try solve [
      repeat first [ intros; eapply @PositiveContextOk
                   | progress split_andb
                   | congruence
                   | tauto
                   | solve [ auto | eapply @BinPos.Pos.eqb_eq; auto ]
                   | eapply @Wf_from_unit
                   | eapply @dec_rel_of_bool_dec_rel
                   | eapply @internal_base_type_dec_lb
                   | eapply @internal_base_type_dec_bl
                   | eapply @InterpEliminateDeadCode; [ .. | eassumption | eassumption | ]
                   | progress intros
                   | rewrite !@lookupb_empty
                   | eapply @wf_from_unit with (uContext:=PContext _); [ .. | eassumption ]
                   | lazymatch goal with
                     | [ |- Some _ = Some _ ] => fail
                     | [ |- None = Some _ ] => exfalso; eapply @wf_interp_not_None; [ .. | unfold Syntax.Named.Interp in *; eassumption ]
                     | [ |- ?x = Some _ ] => destruct x eqn:?; [ apply f_equal | ]
                     end ] ].
    { lazymatch goal with
      | [ H : DeadCodeElimination.EliminateDeadCode _ _ = Some ?e |- Syntax.Named.Interp ?e _ = Some _ ]
        => let lhs := match goal with |- ?lhs = _ => lhs end in
           let v := fresh in
           destruct lhs as [v|] eqn:?; [ apply f_equal; eapply @InterpEliminateDeadCode; [ .. | eassumption | try eassumption | try eassumption ]; clear H | ]
      end;
        try solve [       repeat first [ intros; eapply @PositiveContextOk
                                       | eassumption
                   | progress split_andb
                   | congruence
                   | tauto
                   | solve [ auto | eapply @BinPos.Pos.eqb_eq; auto ]
                   | eapply @Wf_from_unit
                   | eapply @dec_rel_of_bool_dec_rel
                   | eapply @internal_base_type_dec_lb
                   | eapply @internal_base_type_dec_bl
                   | eapply @InterpEliminateDeadCode; [ .. | eassumption | eassumption | ]
                   | progress intros
                   | rewrite !@lookupb_empty
                   | eapply @wf_from_unit with (uContext:=PContext _); [ .. | eassumption ]
                   | lazymatch goal with
                     | [ |- Some _ = Some _ ] => fail
                     | [ |- None = Some _ ] => exfalso; eapply @wf_interp_not_None; [ .. | unfold Syntax.Named.Interp in *; eassumption ]
                     | [ |- ?x = Some _ ] => destruct x eqn:?; [ apply f_equal | ]
                     end ] ].
      lazymatch goal with
      | [ H : DeadCodeElimination.EliminateDeadCode _ _ = Some ?e |- Syntax.Named.Interp ?e _ = Some _ ]
        => let lhs := match goal with |- ?lhs = _ => lhs end in
           let v := fresh in
           destruct lhs as [v|] eqn:?; [ apply f_equal; eapply @InterpEliminateDeadCode; [ .. | eassumption | try eassumption | try eassumption ]; clear H | ]
      | [ |- Syntax.Named.Interp (RewriteAddToAdc.rewrite_expr _ ?e) _ = Some _ ]
        => let lhs := match goal with |- ?lhs = _ => lhs end in
           let H := fresh in
           destruct lhs eqn:H; [ apply (f_equal (@Some _)); eapply @Interp_rewrite_expr in H | ]
      end;
        try solve [       repeat first [ intros; eapply @PositiveContextOk
                                       | eassumption
                   | progress split_andb
                   | congruence
                   | tauto
                   | solve [ auto | eapply @BinPos.Pos.eqb_eq; auto ]
                   | eapply @Wf_from_unit
                   | eapply @dec_rel_of_bool_dec_rel
                   | eapply @internal_base_type_dec_lb
                   | eapply @internal_base_type_dec_bl
                   | eapply @InterpEliminateDeadCode; [ .. | eassumption | eassumption | ]
                   | progress intros
                   | rewrite !@lookupb_empty
                   | eapply @wf_from_unit with (uContext:=PContext _); [ .. | eassumption ]
                   | lazymatch goal with
                     | [ |- Some _ = Some _ ] => fail
                     | [ |- None = Some _ ] => exfalso; eapply @wf_interp_not_None; [ .. | unfold Syntax.Named.Interp in *; eassumption ]
                     | [ |- ?x = Some _ ] => destruct x eqn:?; [ apply f_equal | ]
                     end ] ].
      move e at bottom.
      move e1 at bottom.
      clear dependent e1.

  Admitted.
End language.
