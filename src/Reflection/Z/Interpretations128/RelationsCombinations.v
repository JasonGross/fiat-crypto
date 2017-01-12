Require Import Coq.ZArith.ZArith.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Reflection.Z.InterpretationsGen.
Require Import Crypto.Reflection.Z.Interpretations128.
Require Import Crypto.Reflection.Z.Interpretations128.Relations.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.

Module Relations.
  Local Ltac t_proj_step R :=
    match goal with
    | _ => progress simpl in *
    | _ => reflexivity
    | _ => progress destruct_head unit
    | _ => progress destruct_head and
    | _ => progress inversion_option
    | _ => progress inversion_prod
    | _ => progress subst
    | [ H : forall _ _, _ <-> _ |- _ ] => rewrite H
    | _ => progress unfold R
    | _ => intro
    | [ |- _ <-> _ ] => split
    | [ |- _ /\ _ ] => split
    | _ => progress destruct_head prod
    | _ => progress unfold LiftOption.of' in *
    end.
  Local Ltac t_proj R := repeat t_proj_step R.

  Section proj.
    Context {interp_base_type1 interp_base_type2}
            (proj : forall t : base_type, interp_base_type1 t -> interp_base_type2 t).

    Let R {t : flat_type base_type} f g :=
      SmartVarfMap (t:=t) proj f = g.

    Definition interp_type_rel_pointwise2_proj
               {t : type base_type}
      : interp_type interp_base_type1 t -> interp_type interp_base_type2 t -> Prop
      := match t return interp_type interp_base_type1 t -> interp_type interp_base_type2 t -> Prop with
         | Arrow A B
           => fun f g
              => forall x : interp_flat_type interp_base_type1 A,
                  let y := SmartVarfMap proj x in
                  let fx := f x in
                  let gy := g y in
                  @R _ fx gy
         end.

    Lemma interp_flat_type_rel_pointwise2_proj_iff
          {t : flat_type base_type}
          {f : interp_flat_type interp_base_type1 t}
          {g}
      : interp_flat_type_rel_pointwise2 (t:=t) (fun t => @R (Tbase _)) f g
        <-> R f g.
    Proof. induction t; t_proj (@R). Qed.

    Lemma interp_type_rel_pointwise2_proj_iff
          {t : type base_type}
          {f : interp_type interp_base_type1 t}
          {g}
      : interp_type_rel_pointwise2 (t:=t) (fun t => @R (Tbase _)) f g
        <-> interp_type_rel_pointwise2_proj (t:=t) f g.
    Proof.
      destruct t; simpl; unfold Morphisms.respectful_hetero.
      setoid_rewrite interp_flat_type_rel_pointwise2_proj_iff; unfold R.
      split; intros; subst; auto.
    Qed.
  End proj.

  Section proj_option.
    Context {interp_base_type1 : Type} {interp_base_type2 : base_type -> Type}
            (proj_option : forall t, interp_base_type1 -> interp_base_type2 t).

    Let R {t : flat_type base_type} f g :=
      let f' := LiftOption.of' (t:=t) f in
      match f' with
      | Some f' => SmartVarfMap proj_option f' = g
      | None => True
      end.

    Definition interp_type_rel_pointwise2_proj_option
               {t : type base_type}
      : interp_type (LiftOption.interp_base_type' interp_base_type1) t -> interp_type interp_base_type2 t -> Prop
      := match t return interp_type (LiftOption.interp_base_type' interp_base_type1) t -> interp_type interp_base_type2 t -> Prop  with
         | Arrow A B
           => fun f g
              => forall x : interp_flat_type (fun _ => interp_base_type1) A,
                  let y := SmartVarfMap proj_option x in
                  let fx := f (LiftOption.to' (Some x)) in
                  let gy := g y in
                  @R _ fx gy
         end.

    Lemma interp_flat_type_rel_pointwise2_proj_option_iff
          {t : flat_type base_type}
          {f : interp_flat_type (LiftOption.interp_base_type' interp_base_type1) t}
          {g}
      : interp_flat_type_rel_pointwise2 (t:=t) (fun t => @R (Tbase _)) f g
        <-> R f g.
    Proof. induction t; t_proj (@R);
             repeat (break_match; t_proj (@R);
               break_match_hyps; t_proj (@R)).

           repeat break_innermost_match.
           unfold LiftOption.of'; simpl.
           unfold LiftOption.of' in *.
           t_proj (@R).
    Qed.

    Lemma uncurry_interp_type_rel_pointwise2_proj
          {t : type base_type}
          {f : interp_type interp_base_type1 t}
          {g}
      : interp_type_rel_pointwise2 (t:=t) (fun t => @R (Tbase _)) f g
        <-> interp_type_rel_pointwise2_proj (t:=t) f g.
    Proof.
      destruct t; simpl; unfold Morphisms.respectful_hetero.
      setoid_rewrite uncurry_interp_flat_type_rel_pointwise2_proj; unfold R.
      split; intros; subst; auto.
    Qed.
    Lemma uncurry_interp_type_rel_pointwise2_proj_option
          {t : type base_type}
          {f : interp_type (LiftOption.interp_base_type' interp_base_type1) t}
          {g}
      : interp_type_rel_pointwise2 (t:=t) (fun t => @R _) f g
        -> interp_type_rel_pointwise2_uncurried_proj_option (t:=t) f g.
    Proof.
      unfold interp_type_rel_pointwise2_uncurried_proj_option.
      induction t as [t|A B IHt]; simpl; unfold Morphisms.respectful_hetero in *.
      { induction t as [t| |A IHA B IHB]; simpl; destruct_head_hnf' unit;
          [ solve [ trivial | reflexivity ] | reflexivity | ].
        intros [HA HB].
        specialize (IHA _ _ HA); specialize (IHB _ _ HB).
        unfold R in *.
        repeat first [ progress destruct_head_hnf' prod
                     | progress simpl in *
                     | progress unfold LiftOption.of' in *
                     | progress break_match
                     | progress break_match_hyps
                     | progress inversion_prod
                     | progress inversion_option
                     | reflexivity
                     | progress intuition subst ]. }
      { destruct B; intros H ?; apply IHt, H; clear IHt.
        { repeat first [ progress simpl in *
                       | progress unfold R, LiftOption.of' in *
                       | progress break_match
                       | reflexivity ]. }
        { simpl in *; break_match; reflexivity. } }
    Qed.
  End proj_option.

  Section proj_option2.
    Context {interp_base_type1 : Type} {interp_base_type2 : Type}
            (proj : interp_base_type1 -> interp_base_type2).

    Let R {t : flat_type base_type} f g :=
      let f' := LiftOption.of' (t:=t) f in
      let g' := LiftOption.of' (t:=t) g in
      match f', g' with
      | Some f', Some g' => SmartVarfMap (fun _ => proj) f' = g'
      | None, None => True
      | Some _, _ => False
      | None, _ => False
      end.

    Definition interp_type_rel_pointwise2_uncurried_proj_option2
               {t : type base_type}
      : interp_type (LiftOption.interp_base_type' interp_base_type1) t -> interp_type (LiftOption.interp_base_type' interp_base_type2) t -> Prop
      := match t return interp_type (LiftOption.interp_base_type' interp_base_type1) t -> interp_type (LiftOption.interp_base_type' interp_base_type2) t -> Prop  with
         | Tflat T => @R _
         | Arrow A B
           => fun f g
              => forall x : interp_flat_type (fun _ => interp_base_type1) (all_binders_for (Arrow A B)),
                  let y := SmartVarfMap (fun _ => proj) x in
                  let fx := f (LiftOption.to' (Some x)) in
                  let gy := g (LiftOption.to' (Some y)) in
                  @R _ fx gy
         end.

    Lemma uncurry_interp_type_rel_pointwise2_proj_option2
          {t : type base_type}
          {f : interp_type (LiftOption.interp_base_type' interp_base_type1) t}
          {g : interp_type (LiftOption.interp_base_type' interp_base_type2) t}
      : interp_type_rel_pointwise2 (t:=t) (fun t => @R _) f g
        -> interp_type_rel_pointwise2_uncurried_proj_option2 (t:=t) f g.
    Proof.
      unfold interp_type_rel_pointwise2_uncurried_proj_option2.
      induction t as [t|A B IHt]; simpl; unfold Morphisms.respectful_hetero in *.
      { induction t as [t| |A IHA B IHB]; simpl; destruct_head_hnf' unit;
          [ solve [ trivial | reflexivity ] | reflexivity | ].
        intros [HA HB].
        specialize (IHA _ _ HA); specialize (IHB _ _ HB).
        unfold R in *.
        repeat first [ progress destruct_head_hnf' prod
                     | progress simpl in *
                     | progress unfold LiftOption.of' in *
                     | progress break_match
                     | progress break_match_hyps
                     | progress inversion_prod
                     | progress inversion_option
                     | reflexivity
                     | progress intuition subst ]. }
      { destruct B; intros H ?; apply IHt, H; clear IHt.
        { repeat first [ progress simpl in *
                       | progress unfold R, LiftOption.of' in *
                       | progress break_match
                       | reflexivity ]. }
        { simpl in *; break_match; reflexivity. } }
    Qed.
  End proj_option2.

  Section proj_from_option2.
    Context {interp_base_type0 : Type} {interp_base_type1 interp_base_type2 : base_type -> Type}
            (proj01 : forall t, interp_base_type0 -> interp_base_type1 t)
            (proj02 : forall t, interp_base_type0 -> interp_base_type2 t)
            (proj : forall t, interp_base_type1 t -> interp_base_type2 t).

    Let R {t : flat_type base_type} f g :=
      proj_eq_rel (SmartVarfMap proj (t:=t)) f g.

    Definition interp_type_rel_pointwise2_uncurried_proj_from_option2
               {t : type base_type}
      : interp_type (LiftOption.interp_base_type' interp_base_type0) t -> interp_type interp_base_type1 t -> interp_type interp_base_type2 t -> Prop
      := match t return interp_type _ t -> interp_type _ t -> interp_type _ t -> Prop  with
         | Tflat T => fun f0 f g => match LiftOption.of' f0 with
                                    | Some _ => True
                                    | None => False
                                    end -> @R _ f g
         | Arrow A B
           => fun f0 f g
              => forall x : interp_flat_type (fun _ => interp_base_type0) (all_binders_for (Arrow A B)),
                  let x' := SmartVarfMap proj01 x in
                  let y' := SmartVarfMap proj x' in
                  let fx := f x' in
                  let gy := g y' in
                  let f0x := LiftOption.of' (f0 (LiftOption.to' (Some x))) in
                  match f0x with
                  | Some _ => True
                  | None => False
                  end
                  -> @R _ fx gy
         end.

    Lemma uncurry_interp_type_rel_pointwise2_proj_from_option2
          {t : type base_type}
          {f0}
          {f : interp_type interp_base_type1 t}
          {g : interp_type interp_base_type2 t}
          (proj012 : forall t x, proj t (proj01 t x) = proj02 t x)
      : interp_type_rel_pointwise2 (t:=t) (LiftOption.lift_relation (fun t => proj_eq_rel (proj01 t))) f0 f
        -> interp_type_rel_pointwise2 (t:=t) (LiftOption.lift_relation (fun t => proj_eq_rel (proj02 t))) f0 g
        -> interp_type_rel_pointwise2_uncurried_proj_from_option2 (t:=t) f0 f g.
    Proof.
      unfold interp_type_rel_pointwise2_uncurried_proj_from_option2.
      induction t as [t|A B IHt]; simpl; unfold Morphisms.respectful_hetero in *.
      { induction t as [t| |A IHA B IHB]; simpl; destruct_head_hnf' unit; try reflexivity.
        { cbv [LiftOption.lift_relation proj_eq_rel R].
          break_match; try tauto; intros; subst.
          apply proj012. }
        { intros [HA HB] [HA' HB'] Hrel.
          specialize (IHA _ _ _ HA HA'); specialize (IHB _ _ _ HB HB').
          unfold R, proj_eq_rel in *.
          repeat first [ progress destruct_head_hnf' prod
                       | progress simpl in *
                       | progress unfold LiftOption.of' in *
                       | progress break_match
                       | progress break_match_hyps
                       | progress inversion_prod
                       | progress inversion_option
                       | reflexivity
                       | progress intuition subst ]. } }
      { destruct B; intros H0 H1 ?; apply IHt; clear IHt; first [ apply H0 | apply H1 ];
          repeat first [ progress simpl in *
                       | progress unfold R, LiftOption.of', proj_eq_rel, LiftOption.lift_relation in *
                       | break_match; rewrite <- ?proj012; reflexivity ]. }
    Qed.
  End proj_from_option2.
  Global Arguments uncurry_interp_type_rel_pointwise2_proj_from_option2 {_ _ _ _ _} proj {t f0 f g} _ _ _.

  Section proj1_from_option2.
    Context {interp_base_type0 interp_base_type1 : Type} {interp_base_type2 : base_type -> Type}
            (proj01 : interp_base_type0 -> interp_base_type1)
            (proj02 : forall t, interp_base_type0 -> interp_base_type2 t)
            (R : forall t, interp_base_type1 -> interp_base_type2 t -> Prop).

    Definition interp_type_rel_pointwise2_uncurried_proj1_from_option2
               {t : type base_type}
      : interp_type (LiftOption.interp_base_type' interp_base_type0) t -> interp_type (LiftOption.interp_base_type' interp_base_type1) t -> interp_type interp_base_type2 t -> Prop
      := match t return interp_type _ t -> interp_type _ t -> interp_type _ t -> Prop  with
         | Tflat T => fun f0 f g => match LiftOption.of' f0 with
                                    | Some _ => True
                                    | None => False
                                    end -> match LiftOption.of' f with
                                           | Some f' => interp_flat_type_rel_pointwise2 (@R) f' g
                                           | None => True
                                           end
         | Arrow A B
           => fun f0 f g
              => forall x : interp_flat_type (fun _ => interp_base_type0) (all_binders_for (Arrow A B)),
                  let x' := SmartVarfMap (fun _ => proj01) x in
                  let y' := SmartVarfMap proj02 x in
                  let fx := LiftOption.of' (f (LiftOption.to' (Some x'))) in
                  let gy := g y' in
                  let f0x := LiftOption.of' (f0 (LiftOption.to' (Some x))) in
                  match f0x with
                  | Some _ => True
                  | None => False
                  end
                  -> match fx with
                     | Some fx' => interp_flat_type_rel_pointwise2 (@R) fx' gy
                     | None => True
                     end
         end.

    Lemma uncurry_interp_type_rel_pointwise2_proj1_from_option2
          {t : type base_type}
          {f0}
          {f : interp_type (LiftOption.interp_base_type' interp_base_type1) t}
          {g : interp_type interp_base_type2 t}
          (proj012R : forall t x, @R _ (proj01 x) (proj02 t x))
      : interp_type_rel_pointwise2 (t:=t) (LiftOption.lift_relation2 (proj_eq_rel proj01)) f0 f
        -> interp_type_rel_pointwise2 (t:=t) (LiftOption.lift_relation (fun t => proj_eq_rel (proj02 t))) f0 g
        -> interp_type_rel_pointwise2_uncurried_proj1_from_option2 (t:=t) f0 f g.
    Proof.
      unfold interp_type_rel_pointwise2_uncurried_proj1_from_option2.
      induction t as [t|A B IHt]; simpl; unfold Morphisms.respectful_hetero in *.
      { induction t as [t| |A IHA B IHB]; simpl; destruct_head_hnf' unit; try reflexivity.
        { cbv [LiftOption.lift_relation proj_eq_rel LiftOption.lift_relation2].
          break_match; try tauto; intros; subst.
          apply proj012R. }
        { intros [HA HB] [HA' HB'] Hrel.
          specialize (IHA _ _ _ HA HA'); specialize (IHB _ _ _ HB HB').
          unfold proj_eq_rel in *.
          repeat first [ progress destruct_head_hnf' prod
                       | progress simpl in *
                       | progress unfold LiftOption.of' in *
                       | progress break_match
                       | progress break_match_hyps
                       | progress inversion_prod
                       | progress inversion_option
                       | reflexivity
                       | progress intuition subst ]. } }
      { destruct B; intros H0 H1 ?; apply IHt; clear IHt; first [ apply H0 | apply H1 ];
          repeat first [ progress simpl in *
                       | progress unfold R, LiftOption.of', proj_eq_rel, LiftOption.lift_relation in *
                       | break_match; reflexivity ]. }
    Qed.
  End proj1_from_option2.
  Global Arguments uncurry_interp_type_rel_pointwise2_proj1_from_option2 {_ _ _ _ _} R {t f0 f g} _ _ _.

  Section combine_related.
    Lemma related_flat_transitivity {interp_base_type1 interp_base_type2 interp_base_type3}
          {R1 : forall t : base_type, interp_base_type1 t -> interp_base_type2 t -> Prop}
          {R2 : forall t : base_type, interp_base_type1 t -> interp_base_type3 t -> Prop}
          {R3 : forall t : base_type, interp_base_type2 t -> interp_base_type3 t -> Prop}
          {t x y z}
    : (forall t a b c, (R1 t a b : Prop) -> (R2 t a c : Prop) -> (R3 t b c : Prop))
      -> interp_flat_type_rel_pointwise2 (t:=t) R1 x y
      -> interp_flat_type_rel_pointwise2 (t:=t) R2 x z
      -> interp_flat_type_rel_pointwise2 (t:=t) R3 y z.
    Proof.
      intro HRel; induction t; simpl; intuition eauto.
    Qed.
  End combine_related.
End Relations.
