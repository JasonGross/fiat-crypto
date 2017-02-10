Require Export Crypto.Specific.GF25519Reflective.Common.
Require Import Crypto.Specific.GF25519BoundedCommon.
Require Import Crypto.Reflection.Z.Interpretations64.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Util.Tactics.

Local Opaque Interp.
Lemma ExprBinOp_correct_and_bounded
      ropZ op (ropZ_sig : rexpr_binop_sig op)
      (Hbounds : correct_and_bounded_genT ropZ ropZ_sig)
      (*(H0 : forall xy
                   (xy := (eta_fe25519W (fst xy), eta_fe25519W (snd xy)))
                   (Hxy : is_bounded (fe25519WToZ (fst xy)) = true
                          /\ is_bounded (fe25519WToZ (snd xy)) = true),
          let Hx := let (Hx, Hy) := Hxy in Hx in
          let Hy := let (Hx, Hy) := Hxy in Hy in
          let args := binop_args_to_bounded xy Hx Hy in
          match LiftOption.of'
                  (ApplyInterpedAll (Interp (@BoundedWordW.interp_op) ropW)
                                    (LiftOption.to' (Some args)))
          with
          | Some _ => True
          | None => False
          end)
      (H1 : forall xy
                   (xy := (eta_fe25519W (fst xy), eta_fe25519W (snd xy)))
                   (Hxy : is_bounded (fe25519WToZ (fst xy)) = true
                          /\ is_bounded (fe25519WToZ (snd xy)) = true),
          let Hx := let (Hx, Hy) := Hxy in Hx in
          let Hy := let (Hx, Hy) := Hxy in Hy in
          let args := binop_args_to_bounded (fst xy, snd xy) Hx Hy in
          let x' := SmartVarfMap (fun _ : base_type => BoundedWordW.BoundedWordToBounds) args in
          match LiftOption.of'
                  (ApplyInterpedAll (Interp (@ZBounds.interp_op) ropW) (LiftOption.to' (Some x')))
          with
          | Some bounds => binop_bounds_good bounds = true
          | None => False
          end)*)
  : binop_correct_and_bounded ropZ op.
Proof.
  intros xy HxHy.
  cbv zeta in Hbounds.
  destruct_head' and.
  subst; rewrite <- (proj2_sig ropZ_sig).
  unfold Relations.related_wordW, Relations.related_bounds, Relations.related_Z in *.
  eapply LiftOption.lift_relation_type_pointwise in H0.
  eapply LiftOption.lift_relation_type_pointwise in H2.
  eapply LiftOption.lift_relation2_type_pointwise in H1.
  { setoid_rewrite Relations.lift_interp_type_rel_pointwise_f_eq_id2 in H0.
    setoid_rewrite Relations.lift_interp_type_rel_pointwise_f_eq_id2 in H2.
    setoid_rewrite Relations.lift_interp_type_rel_pointwise_f_eq_id2 in H1.
    cbv [ExprBinOpT] in *.
    simpl @interp_flat_type in *.
    specialize (H0 xy).

  unfold Relations.related'_Z in *.
  unfold Relations.proj_eq_rel in *.
  Locate LiftOption.lift_relation.

  Check LiftOption.of'.
  unfold interp_type_rel_pointwise, interp_type_gen_rel_pointwise, interp_type_gen_rel_pointwise_hetero, ExprBinOpT, Morphisms.respectful_hetero, interp_flat_type_rel_pointwise, interp_flat_type_rel_pointwise_gen_Prop in *.
  simpl @interp_flat_type in *.
  cbv

  simpl in x, y, Hx, Hy.

  simpl in HxHy.
  pose x as x'; pose y as y'.
  hnf in x, y; destruct_head' prod.
  specialize (H0 (x', y') (conj Hx Hy)).
  specialize (H1 (x', y') (conj Hx Hy)).
  let args := constr:(binop_args_to_bounded (x', y') Hx Hy) in
  t_correct_and_bounded ropZ_sig Hbounds H0 H1 args.
Qed.
