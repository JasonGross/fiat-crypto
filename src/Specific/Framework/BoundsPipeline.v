Require Import Coq.ZArith.BinIntDef.
Require Import Coq.omega.Omega.
Require Import Coq.micromega.Lia.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Compilers.Z.Bounds.Pipeline.Definition.
Require Import Crypto.Compilers.Z.Bounds.Pipeline.ReflectiveTactics.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Tuple.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Tuple.
Require Import Crypto.Util.SideConditions.CorePackages.
Require Import Crypto.Util.SideConditions.ReductionPackages.
Require Import Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
Require Import Crypto.Specific.Framework.OutputType.
Require Import Crypto.Specific.Framework.OutputTypeLemmas.
Require Import Crypto.Specific.Framework.BoundsPipelineInputSideConditions.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.ZUtil.Tactics.PeelLe.
Require Import Crypto.Util.ZUtil.Tactics.ReplaceNegWithPos.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.
Import CurveParameters.Notations.

Local Set Implicit Arguments.
Local Coercion Z.to_nat : Z >-> nat.
Local Notation interp_flat_type := (interp_flat_type interp_base_type).

Section gen.
  Context (curve : CurveParameters.CurveParameters)
          (curve_sc : CurveParameterBaseSideConditions curve)
          (ropsZ : SynthesisOutputOps curve TZ)
          (P_extra : SynthesisOutputProps curve TZ)
          (HP_extra : SynthesisOutputOpsValid' ropsZ P_extra)
          (curve_scib : BoundsInputSideConditions ropsZ P_extra).

  Let anf := {| Pipeline.Definition.anf := true |}.
  (** N.B. These might one day context variables if we want to set them elsewhere. *)
  Let carry_opts : PipelineOptions := default_PipelineOptions.
  Let add_sub_opp_opts : PipelineOptions := default_PipelineOptions.
  Let mul_square_opts : PipelineOptions := default_PipelineOptions.
  Let freeze_opts : PipelineOptions := anf.
  Let nonzero_opts : PipelineOptions := anf.

  Local Notation wt := curve.(wt).
  Local Notation lgwt := curve.(lgwt).
  Local Notation m := curve.(m).
  Local Notation sz := curve.(sz).
  Local Notation bitwidth := curve.(bitwidth).
  Local Notation allowable_bit_widths := curve.(allowable_bit_widths).
  Local Notation freeze_allowable_bit_widths := curve.(freeze_allowable_bit_widths).
  Local Notation bounds_tight := curve.(bounds_tight).
  Local Notation bounds_loose := curve.(bounds_loose).
  Local Notation bounds_limb_widths := curve.(bounds_limb_widths).
  Local Notation bound1 := curve.(bound1).

  Local Notation TW := (TWord (Z.log2_up bitwidth)).
  Local Notation tZ := (Tbase TZ).
  Local Notation tW := (Tbase TW).
  Local Notation RT := (curve.(RT)).
  Local Notation rT := (curve.(rT)).
  Local Notation RTZ := (RT TZ).
  Local Notation rTZ := (rT TZ).
  Local Notation RTW := (RT TW).
  Local Notation rTW := (rT TW).
  Local Notation T' := curve.(T').
  Local Notation carryZ := ropsZ.(carry).
  Local Notation addZ := ropsZ.(add).
  Local Notation subZ := ropsZ.(sub).
  Local Notation oppZ := ropsZ.(opp).
  Local Notation carry_mulZ := ropsZ.(carry_mul).

  Local Notation allowable_lgsz := (List.map Nat.log2 allowable_bit_widths).

  Local Notation pick_typeb := (@Interpretation.Bounds.bounds_to_base_type (Interpretation.Bounds.round_up_to_in_list allowable_lgsz)) (only parsing).
  Local Notation pick_type v := (SmartFlatTypeMap pick_typeb v).

  Local Notation bounds_tightZ := curve.(bounds_tightZ).
  Local Notation bounds_looseZ := curve.(bounds_looseZ).

  Local Notation exprT n
    := (fun b : base_type => ((rT b)^n%nat -> (rT b))%ctype).
  Local Notation exprT1 n
    := (fun b : base_type => ((rT b)^n%nat -> Tbase b)%ctype).

  Record RBPipelineSideConditions
         (T : base_type -> _)
         (fZ : Expr (T TZ))
         (inbounds : Syntax.interp_flat_type _ (domain (T TZ)))
         (outbounds : Syntax.interp_flat_type _ (codomain (T TZ)))
         opts :=
    {
      RBEvars :> _;
      RBSideConditions
      : (forall
            (v' : interp_flat_type (pick_type inbounds))
            (Hv : Interpretation.Bounds.is_bounded_by inbounds (cast_back_flat_const v')),
            { final_e_evar
              : interp_flat_type (pick_type outbounds)
                & @PipelineSideConditions
                    allowable_lgsz opts (T TZ) inbounds outbounds v' _ final_e_evar RBEvars
                    (exist _ fZ (fun _ => eq_refl)) });
      RBVal :> cast_evar_package (e_final_newtype (PipelineEvars:=RBEvars)) (Expr (T TW))
    }.

  Record BoundsSideConditions :=
    {
      encode0W : vm_compute_evar_package_vm_small (curve.(encodeTuple) TW (ropsZ.(encodeZ) 0%F));
      encode1W : vm_compute_evar_package_vm_small (curve.(encodeTuple) TW (ropsZ.(encodeZ) 1%F));
      carryW_side_conditions
      : @RBPipelineSideConditions
          (exprT 1) (ropsZ.(carry)) bounds_looseZ bounds_tightZ
          carry_opts;
      addW_side_conditions
      : @RBPipelineSideConditions
          (exprT 2) (ropsZ.(add)) (bounds_tightZ, bounds_tightZ) bounds_looseZ
          add_sub_opp_opts;
      subW_side_conditions
      : @RBPipelineSideConditions
          (exprT 2) (ropsZ.(sub)) (bounds_tightZ, bounds_tightZ) bounds_looseZ
          add_sub_opp_opts;
      oppW_side_conditions
      : @RBPipelineSideConditions
          (exprT 1) (ropsZ.(opp)) bounds_tightZ bounds_looseZ
          add_sub_opp_opts;
      carry_mulW_side_conditions
      : @RBPipelineSideConditions
          (exprT 2) (ropsZ.(carry_mul)) (bounds_looseZ, bounds_looseZ) bounds_tightZ
          mul_square_opts;
      carry_squareW_side_conditions
      : @RBPipelineSideConditions
          (exprT 1) (ropsZ.(carry_square)) bounds_looseZ bounds_tightZ
          mul_square_opts;
      freezeW_side_conditions
      : match ropsZ.(freeze) with
        | Some freezeZ
          => @RBPipelineSideConditions
               (exprT 1) freezeZ bounds_tightZ bounds_tightZ
               freeze_opts
        | None => vm_decide_package (curve.(CurveParameters.freeze) = false)
        end;
      nonzeroW_side_conditions
      : match ropsZ.(nonzero) with
        | Some nonzeroZ
          => @RBPipelineSideConditions
               (exprT1 1) nonzeroZ bounds_tightZ bound1
               nonzero_opts
        | None => vm_decide_package (curve.(CurveParameters.montgomery) = false)
        end;
    }.

  Context (curve_scb : BoundsSideConditions).

  Local Ltac interposeW f :=
    etransitivity; [ | etransitivity ];
    [ | eapply f; assumption | ];
    [ cbv [decode tuple_map SmartVarfMap smart_interp_flat_map];
      apply f_equal; rewrite !Tuple.map_id
    | cbv [decode tuple_map SmartVarfMap smart_interp_flat_map];
      rewrite !flat_interp_tuple_untuple, !Tuple.map_map; reflexivity ].

  (*Lemma generalize_bounds bounds1 bounds2
    : forall f : interp_type interp_base_type (rTZ -> rTZ),
      (forall v' : interp_flat_type (pick_type (flat_interp_untuple bounds1)),
          Interpretation.Bounds.is_bounded_by (flat_interp_untuple bounds1) (cast_back_flat_const v') ->
          Interpretation.Bounds.is_bounded_by (flat_interp_untuple bounds2) (f (cast_back_flat_const v'))) ->
      forall x : T' TZ,
        ZRange.is_bounded_by None bounds1 (flat_interp_tuple x) ->
        ZRange.is_bounded_by None bounds2 (flat_interp_tuple (f x)).
  Proof.
    cbv [Interpretation.Bounds.is_bounded_by Interpretation.Bounds.is_bounded_by' ZRange.is_bounded_by].
    intros f H x H0.

    cbv [ZRange.is_bounded_by'] in *.*)

  Lemma generalize_bounds_loose_tight
    : forall f : interp_type interp_base_type (rTZ -> rTZ),
      (forall v' : interp_flat_type (pick_type bounds_looseZ),
          Interpretation.Bounds.is_bounded_by bounds_looseZ (cast_back_flat_const v') ->
          Interpretation.Bounds.is_bounded_by bounds_tightZ (f (cast_back_flat_const v'))) ->
      forall x : T' TZ,
        ZRange.is_bounded_by None bounds_loose (flat_interp_tuple x) ->
        ZRange.is_bounded_by None bounds_tight (flat_interp_tuple (f x)).
  Proof.
    cbv [bounds_looseZ bounds_tightZ].
    cbv [Interpretation.Bounds.is_bounded_by Interpretation.Bounds.is_bounded_by' ZRange.is_bounded_by].
  Admitted.

  Lemma generalize_bounds_tight_loose
    : forall f : interp_type interp_base_type (rTZ -> rTZ),
      (forall v' : interp_flat_type (pick_type bounds_tightZ),
          Interpretation.Bounds.is_bounded_by bounds_tightZ (cast_back_flat_const v') ->
          Interpretation.Bounds.is_bounded_by bounds_looseZ (f (cast_back_flat_const v'))) ->
      forall x : T' TZ,
        ZRange.is_bounded_by None bounds_tight (flat_interp_tuple x) ->
        ZRange.is_bounded_by None bounds_loose (flat_interp_tuple (f x)).
  Proof.
    cbv [Interpretation.Bounds.is_bounded_by Interpretation.Bounds.is_bounded_by' ZRange.is_bounded_by].
  Admitted.

  Lemma generalize_bounds_tight_tight
    : forall f : interp_type interp_base_type (rTZ -> rTZ),
      (forall v' : interp_flat_type (pick_type bounds_tightZ),
          Interpretation.Bounds.is_bounded_by bounds_tightZ (cast_back_flat_const v') ->
          Interpretation.Bounds.is_bounded_by bounds_tightZ (f (cast_back_flat_const v'))) ->
      forall x : T' TZ,
        ZRange.is_bounded_by None bounds_tight (flat_interp_tuple x) ->
        ZRange.is_bounded_by None bounds_tight (flat_interp_tuple (f x)).
  Proof.
    cbv [Interpretation.Bounds.is_bounded_by Interpretation.Bounds.is_bounded_by' ZRange.is_bounded_by].
  Admitted.

  Lemma generalize_bounds_tight_bound1
    : forall f : interp_type interp_base_type (rTZ -> tZ),
      (forall v' : interp_flat_type (pick_type bounds_tightZ),
          Interpretation.Bounds.is_bounded_by bounds_tightZ (cast_back_flat_const v') ->
          Interpretation.Bounds.is_bounded_by (T:=Tbase _) bound1 (f (cast_back_flat_const v'))) ->
      forall x : T' TZ,
        ZRange.is_bounded_by None bounds_tight (flat_interp_tuple x) ->
        ZRange.is_bounded_by (n:=1) None bound1 (f x).
  Proof.
    cbv [Interpretation.Bounds.is_bounded_by Interpretation.Bounds.is_bounded_by' ZRange.is_bounded_by].
  Admitted.

  Lemma generalize_bounds_loose2_tight
    : forall f : interp_type interp_base_type (rTZ * rTZ -> rTZ),
      (forall v' : interp_flat_type (pick_type ((bounds_looseZ, bounds_looseZ) : Syntax.interp_flat_type _ (_ * _))),
          Interpretation.Bounds.is_bounded_by (T:=Prod _ _) (bounds_looseZ, bounds_looseZ) (cast_back_flat_const v') ->
          Interpretation.Bounds.is_bounded_by bounds_tightZ (f (cast_back_flat_const v'))) ->
      forall x y : T' TZ,
        ZRange.is_bounded_by None bounds_loose (flat_interp_tuple x) ->
        ZRange.is_bounded_by None bounds_loose (flat_interp_tuple y) ->
        ZRange.is_bounded_by None bounds_tight (flat_interp_tuple (f (x, y))).
  Proof.
    cbv [Interpretation.Bounds.is_bounded_by Interpretation.Bounds.is_bounded_by' ZRange.is_bounded_by].
  Admitted.

  Lemma bounded_eq_map_interp v
        (H : ZRange.is_bounded_by None curve.(bounds_bitwidths) v)
    : Tuple.map (fun x => @interpToZ (TWord (Z.to_nat (Z.log2_up bitwidth))) (ZToInterp x))
                v
      = v.
  Proof.
    setoid_rewrite interpToZ_ZToInterp_mod.
    rewrite <- (Tuple.map_id v).
    cbv [ZRange.is_bounded_by bounds_bitwidths bounds' ZRange.is_bounded_by' ZRange.lower ZRange.upper] in H.
    match goal with |- ?G => cut (G /\ Tuple.fieldwise (fun x y => x = y) v v); [ tauto | ] end.
    rewrite <- Tuple.fieldwise_eq_iff, Tuple.fieldwise_map_iff, Tuple.map_id.
    rewrite Tuple.fieldwise_lift_and.
    lazymatch goal with
    | [ |- Tuple.fieldwise (fun a b => @?H a b /\ a = b) ?v ?v ]
      => cut (Tuple.fieldwise (fun a b => H b b /\ a = b) v v); cbv beta
    end.
    { apply Tuple.fieldwise_Proper; [ intros ?? [? ?]; subst; auto | reflexivity | reflexivity ]. }
    rewrite <- Tuple.fieldwise_lift_and, Tuple.fieldwise_eq_iff; split; [ | reflexivity ].
    revert H.
    rewrite <- (Tuple.map_id v), !Tuple.fieldwise_map_iff.
    apply (@Tuple.fieldwise_Proper_gen_dep _ _ _ _ (fun _ _ => True) eq Basics.impl);
      [ compute; tauto
      | compute; tauto
      | intros; subst
      | rewrite Tuple.fieldwise_to_list_iff, Forall2_forall_iff; rewrite ?Tuple.length_to_list; constructor
      | rewrite Tuple.fieldwise_eq_iff; reflexivity ].
    intros [H' _].
    pose proof (Z.log2_up_nonneg bitwidth).
    rewrite Z.max_r, Z.pow_Zpow, Z2Nat.id by omega; cbn.
    rewrite Z.mod_small; [ omega | split; [ omega | ] ].
    eapply (Z.lt_le_trans _ (2^bitwidth)); [ omega | ].
    Z.peel_le.
    apply Z.log2_up_le_full.
  Qed.

  Lemma generalize_bounds_tight2_loose
    : forall f : interp_type interp_base_type (rTZ * rTZ -> rTZ),
      (forall v' : interp_flat_type (pick_type ((bounds_tightZ, bounds_tightZ) : Syntax.interp_flat_type _ (_ * _))),
          Interpretation.Bounds.is_bounded_by (T:=Prod _ _) (bounds_tightZ, bounds_tightZ) (cast_back_flat_const v') ->
          Interpretation.Bounds.is_bounded_by bounds_looseZ (f (cast_back_flat_const v'))) ->
      forall x y : T' TZ,
        ZRange.is_bounded_by None bounds_tight (flat_interp_tuple x) ->
        ZRange.is_bounded_by None bounds_tight (flat_interp_tuple y) ->
        ZRange.is_bounded_by None bounds_loose (flat_interp_tuple (f (x, y))).
  Proof.
    cbv [Interpretation.Bounds.is_bounded_by Interpretation.Bounds.is_bounded_by' ZRange.is_bounded_by].
  Admitted.

  Import AdmitAxiom.

  Definition BoundsPipeline' : SynthesisOutput curve.
  Proof.
    simple refine
           (let HopsZ_valid := _ in
            let HopsW_valid := _ in
            {|
              opsZ := ropsZ;
              opsW
              := {|
                  encodeZ := ropsZ.(encodeZ);
                  decodeZ := ropsZ.(decodeZ);
                  zero := val curve_scb.(encode0W);
                  one := val curve_scb.(encode1W);
                  carry := val curve_scb.(carryW_side_conditions).(RBVal);
                  add := val curve_scb.(addW_side_conditions).(RBVal);
                  sub := val curve_scb.(subW_side_conditions).(RBVal);
                  opp := val curve_scb.(oppW_side_conditions).(RBVal);
                  carry_mul := val curve_scb.(carry_mulW_side_conditions).(RBVal);
                  carry_square := val curve_scb.(carry_squareW_side_conditions).(RBVal);
                  freeze := match ropsZ.(freeze) as o return match o with Some _ => _ | _ => _ end -> _ with
                            | Some _ => fun freezeW_side_conditions
                                        => Some (val freezeW_side_conditions.(RBVal))
                            | None => fun _ => None
                            end curve_scb.(freezeW_side_conditions);
                  nonzero := match ropsZ.(nonzero) as o return match o with Some _ => _ | _ => _ end -> _ with
                             | Some _ => fun nonzeroW_side_conditions
                                         => Some (val nonzeroW_side_conditions.(RBVal))
                             | None => fun _ => None
                             end curve_scb.(nonzeroW_side_conditions);
                |};
              P_Z
              := {|
                  P_tight x := ZRange.is_bounded_by None bounds_tight (flat_interp_tuple (T:=Tbase TZ) x)
                               /\ P_extra.(P_tight) x;
                  P_loose x := ZRange.is_bounded_by None bounds_loose (flat_interp_tuple x)
                               /\ P_extra.(P_loose) x;
                  P_1 x := ZRange.is_bounded_by' None bound1 x /\ P_extra.(P_1) x;
                  P_relax x pf := conj
                                    (curve_sc.(relax_bounds) (proj1 pf))
                                    (P_extra.(P_relax) x (proj2 pf));
                |};

              opsZ_valid := HopsZ_valid;
              opsW_valid := HopsW_valid;
            |});
      cbn [P_relax P_tight P_loose P_1];
      try clearbody HopsZ_valid;
      try clearbody HopsW_valid.
    { simple refine
             {|
               OutputType.encode_valid v := _
             |};
        cbn [P_tight P_loose];
        try solve [ intros; destruct_head'_and; apply HP_extra; auto
                  | intros; destruct_head'_and; destruct HP_extra; eauto ];
        try (split; destruct_head'_and;
             [ | solve [ apply HP_extra; auto
                       | destruct HP_extra; eauto ] ]);
        try (destruct HP_extra; cbn in *; break_innermost_match_step; intros;
             destruct_head'_and;
             first [ split; [ | solve [ auto ] ]
                   | solve [ auto ] ]).
      { cbv [encode]; rewrite encodeTuple_correct, Tuple.map_id.
        split.
        { apply HP_extra.(encode_bounded). }
        { cbv [Interp interp encodeTuple RT rT].
          cbn; rewrite interpf_SmartPairf, SmartVarfMap_tuple.
          cbv [tuple_map].
          rewrite !flat_interp_tuple_untuple, !Tuple.map_map, Tuple.map_id.
          apply HP_extra.(encode_valid). } }
      { cbv [decode encode]; intro v.
        rewrite decode_encodeTuple_correct, Tuple.map_id.
        apply HP_extra. }
      all:destruct curve_scb;
        repeat match goal with
               | [ H : ?x = Some _, H' : context[?x] |- _ ]
                 => rewrite H in H'
               end;
        destruct_head' RBPipelineSideConditions;
        first [ apply generalize_bounds_loose_tight; [ | assumption.. ]
              | apply generalize_bounds_tight_loose; [ | assumption.. ]
              | apply generalize_bounds_tight_tight; [ | assumption.. ]
              | apply generalize_bounds_loose2_tight; [ | assumption.. ]
              | apply generalize_bounds_tight2_loose; [ | assumption.. ]
              | apply generalize_bounds_tight_bound1; [ | assumption.. ] ];
        repeat match goal with
               | [ H : forall (x : ?A) (y : @?B x), sigT (@?P x y) |- _ ]
                 => let H' := fresh in
                    pose (fun x y => projT1 (H x y)) as H';
                      pose proof (fun x y => (projT2 (H x y) : P x y (H' x y)));
                      clearbody H'; clear H; cbv beta in *
               end;
        lazymatch goal with
        | [ |- forall v : interp_flat_type (pick_type ?inbounds), Interpretation.Bounds.is_bounded_by (T:=?s) _ _ -> Interpretation.Bounds.is_bounded_by (T:=?d) ?outbounds (?f _) ]
          => simple refine
                    (let pf := _ in
                     fun v' Hv'
                     => proj1
                          (@PipelineCorrect
                             _ _ (Arrow s d) inbounds outbounds v' f _ (_ : id _) _ (pf v' Hv')));
               eassumption
        end. }
    { pose proof HopsZ_valid as HopsZ_valid'.
        destruct HopsZ_valid'; unshelve constructor;
        cbn [P_tight P_loose P_1] in *;
        cbv [encode decode] in *;
        cbn [encodeZ decodeZ zero one add sub carry_mul carry_square opp carry freeze nonzero];
        intros.
      all:try match goal with
              | [ |- context[val ?e] ]
                => cbv [val]; destruct e; subst
              end.
      all:try reflexivity.
      1-2:lazymatch goal with
          | [ |- context[encodeZ _ ?v] ]
            => generalize (encode_valid v);
                 cbv [decodeToTuple encodeTuple Interp interp RT rT];
                 cbn; rewrite !interpf_SmartPairf, !SmartVarfMap_tuple;
                   cbv [tuple_map];
                   rewrite !flat_interp_tuple_untuple, !Tuple.map_map;
                   cbn -[interpToZ ZToInterp];
                   cbv [cast_const];
                   change (@ZToInterp TZ) with (@id Z);
                   change (@interpToZ TZ) with (@id Z);
                   cbv [id];
                   rewrite !Tuple.map_id;
                   intros [H0 H1];
                   rewrite ?bounded_eq_map_interp
                     by (auto using curve_sc.(relax_to_bitwidth_bounds), curve_sc.(relax_bounds));
                   auto using HP_extra.(decode_encode_correct)
          | _ => idtac
          end.
      all:admit. }
    { simple refine
             (let Hring :=
                  Ring.ring_by_isomorphism
                    (F := F m)
                    (*(H := interp_flat_type interp_base_type (Tbase TZ^sz))*)
                    (*(phi := fun x => flat_interp_untuple (T:=Tbase TZ) (Positional.Fencode (div_cps:=@div_cps) (modulo_cps:=@modulo_cps) wt x))
                    (phi' := eval')
                    (zero := flat_interp_untuple (T:=Tbase TZ) zeroZ')
                    (one := flat_interp_untuple (T:=Tbase TZ) oneZ')
                    (add := fun x y => Interp carry_addZ' (x, y))
                    (sub := fun x y => Interp carry_subZ' (x, y))
                    (opp := Interp carry_oppZ')
                    (mul := fun x y => Interp carry_mulZ' (x, y))
                    (phi'_opp := eval_carry_oppZ)*)
                    _
                    _
                    _
                    _
                    _ in
              {| ring := proj1 Hring;
                 encode_homomorphism := proj1 (proj2 Hring);
                 decode_homomorphism := proj2 (proj2 Hring);
              |});
        cbv [decode_sig encode_sig carry_opp_sig carry_add_sig carry_sub_sig carry_mul_sig decode_sig carry_opp carry_add carry_sub];
        cbn [P_tight P_loose proj1_sig];
        try reflexivity;
        repeat intros [? [? ?] ]; cbn [proj1_sig];
          repeat rewrite ?EtaInterp.InterpExprEta_arrow, ?LinearizeInterp.InterpLinearize.
      { apply HopsZ_valid. }
      { apply HopsZ_valid. }
      { apply HopsZ_valid. }
      { apply curve_scib.(decode_carry_oppZ); assumption. }
      { apply curve_scib.(decode_carry_addZ); assumption. }
      { apply curve_scib.(decode_carry_subZ); assumption. }
      { apply curve_scib.(decode_carry_mulZ); assumption. } }
    { simple refine
             (let Hring :=
                  Ring.ring_by_isomorphism
                    (F := F m)
                    (*(H := interp_flat_type interp_base_type (Tbase TZ^sz))*)
                    (*(phi := fun x => flat_interp_untuple (T:=Tbase TZ) (Positional.Fencode (div_cps:=@div_cps) (modulo_cps:=@modulo_cps) wt x))
                    (phi' := eval')
                    (zero := flat_interp_untuple (T:=Tbase TZ) zeroZ')
                    (one := flat_interp_untuple (T:=Tbase TZ) oneZ')
                    (add := fun x y => Interp carry_addZ' (x, y))
                    (sub := fun x y => Interp carry_subZ' (x, y))
                    (opp := Interp carry_oppZ')
                    (mul := fun x y => Interp carry_mulZ' (x, y))
                    (phi'_opp := eval_carry_oppZ)*)
                    _
                    _
                    _
                    _
                    _ in
              {| ring := proj1 Hring;
                 encode_homomorphism := proj1 (proj2 Hring);
                 decode_homomorphism := proj2 (proj2 Hring);
              |});
        cbv [decode encode decode_sig carry_opp_sig carry_add_sig carry_sub_sig carry_mul_sig decode_sig carry_opp carry_add carry_sub];
        cbn [P_tight P_loose proj1_sig carry opp add sub carry_mul decodeZ encodeZ];
        try reflexivity;
        try intros [a [Ha0 Ha1] ]; try intros [b [Hb0 Hb1] ]; cbn [proj1_sig].
      { apply HopsW_valid. }
      { apply HopsW_valid. }
      { apply HopsW_valid. }
      all:admit. (*
      { interposeW (curve_scib.(decode_carry_oppZ) _ Ha0 Ha1).
        admit. }
      { interposeW (curve_scib.(decode_carry_addZ) _ _ Ha0 Hb0 Ha1 Hb1).
        admit. }
      { interposeW (curve_scib.(decode_carry_subZ) _ _ Ha0 Hb0 Ha1 Hb1).
        admit. }
      { interposeW (curve_scib.(decode_carry_mulZ) _ _ Ha0 Hb0 Ha1 Hb1).
        admit. } *) }
  Defined.

  Definition BoundsPipeline'' : SynthesisOutput curve.
  Proof.
    let opsZv := (eval hnf in (opsZ BoundsPipeline')) in
    let opsWv := (eval hnf in (opsW BoundsPipeline')) in
    simple refine
           (let opsZref := opsZv in
            let opsZnew := _ in
            let unif_opsZ : opsZref = opsZnew := _ in
            let opsWref := opsWv in
            let opsWnew := _ in
            let Z_and_ring : sigT (fun v => SynthesisOutputOpsRing v) := _ in
            let W_and_ring : sigT (fun v => SynthesisOutputOpsRing v) := _ in
            {| opsZ := opsZnew ; opsW := opsWnew ; P_Z := P_Z BoundsPipeline' ;
               opsZ_ring := projT2 Z_and_ring;
               opsW_ring := projT2 W_and_ring;
            |});
      try clear W_and_right; try clear Z_and_ring;
      try clear unif_opsW; try clear opsWnew;
      try clear unif_opsZ; try clear opsZref; try clear opsZnew.
    { clear -ropsZ; unshelve econstructor; destruct ropsZ; shelve. }
    { destruct ropsZ; cbn in opsZnew; refine eq_refl. }
    all:cbv zeta in *.
    { let v := (eval cbv [freeze val raw_evar_package RBVal encodeZ decodeZ encode1W encode0W addW_side_conditions subW_side_conditions carry_mulW_side_conditions carry_squareW_side_conditions oppW_side_conditions carryW_side_conditions freezeW_side_conditions nonzeroW_side_conditions opsWref] in opsWref) in
      exact v. }
    all:cbv zeta in *; clear opsWref; try clear opsZnew.
    { subst opsZnew.
      abstract (
          generalize (opsZ_ring BoundsPipeline');
          generalize (opsZ_valid BoundsPipeline');
          generalize (P_Z BoundsPipeline');
          cbv [opsZ BoundsPipeline']; destruct ropsZ;
          econstructor; eassumption
        ). }
    { subst opsWnew.
      abstract (econstructor; exact (opsW_ring BoundsPipeline')). }
  Defined.

  Definition BoundsPipeline : SynthesisOutput curve
    := Eval cbv [BoundsPipeline''] in BoundsPipeline''.
End gen.

(** This tactic gets overridden in Pipeline.v, where we actually have
    enough [Require]s to unfold all the things we need to unfold.  It
    would be nice to make an unfold hint database, but [autounfold] is
    orders of magnitude slower than [cbv].  See also
    https://github.com/coq/coq/issues/6144. *)
Ltac RBPipelineSideConditions_unfold := idtac.

Ltac RBPipelineSideConditions_refine_early :=
  cbv [val];
  let evars := open_constr:({| e_pkg := _ |}) in
  simple refine {| RBEvars := evars |};
  [ intros ??; eexists | ].

Ltac RBPipelineSideConditions_match_then_unfold then_tac else_tac :=
  lazymatch goal with
  | [ |- RBPipelineSideConditions _ _ ?expr ?b1 ?b2 ?ops ]
    => let b1' := (eval cbv in b1) in
       let b2' := (eval cbv in b2) in
       let expr' := (eval cbv in expr) in
       change b1 with b1'; change b2 with b2'; change expr with expr';
       RBPipelineSideConditions_unfold;
       then_tac ()
  | [ |- match ?e with Some _ => RBPipelineSideConditions _ _ ?expr ?b1 ?b2 ?ops | None => _ end ]
    => let e' := (eval hnf in e) in
       progress (change e with e'; cbv beta iota);
       RBPipelineSideConditions_match_then_unfold then_tac else_tac
  | _ => else_tac ()
  end.

Ltac autosolve else_tac :=
  RBPipelineSideConditions_match_then_unfold
    ltac:(fun _
          => RBPipelineSideConditions_refine_early;
             [ refine_PipelineSideConditions_constructor;
               solve_post_reified_side_conditions
             | ReductionPackages.autosolve
                 ltac:(fun _ => fail 100 "Internal error in autosolve: expected cast package, but got something that induced a recursive call to autosolve.")
                        else_tac ])
           else_tac.
