Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Tuple.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Bounds.Pipeline.Definition.
Require Import Crypto.Compilers.Z.Bounds.Pipeline.ReflectiveTactics.
Require Import Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
Require Import Crypto.Specific.Framework.OutputType.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Notations.
Import CurveParameters.Notations.

Require Import AdmitAxiom.

Local Coercion Z.to_nat : Z >-> nat.
Local Notation interp_flat_type := (interp_flat_type interp_base_type).

Section with_curve.
  Context (curve : RawCurveParameters.CurveParameters).

  Local Notation RT := (RT curve).
  Local Notation rT := (rT curve).
  Local Notation T' := (T' curve).
  Local Notation encode := (encode curve).
  Local Notation decode := (decode curve).

  Let curve' := fill_defaults_CurveParameters curve.

  Lemma encode_correct b
        (sz_nonzero : curve.(sz) <> 0%nat)
        (sz_small : Z.of_nat curve.(sz) <= Z.log2_up curve.(m))
    : forall v, decode b (Interp (encode b v) tt) = v.
  Proof.
    cbv [decode encode Interp interp codomain RT rT]; intro.
    rewrite interpf_SmartPairf, SmartVarfMap_tuple.
    cbv [SmartVarfMap smart_interp_flat_map tuple_map].
    rewrite !flat_interp_tuple_untuple, !Tuple.map_map.
    cbv [interpf interp_op interpf_step Zinterp_op lift_op SmartFlatTypeMapUnInterp cast_const].
    cbn [interpToZ ZToInterp].
    setoid_rewrite interpToZ_ZToInterp_mod.
    etransitivity;
      [
      | apply Positional.Fdecode_Fencode_id with (weight:=curve.(wt)) (sz:=curve.(sz)) (div:=div) (modulo:=modulo);
        unfold wt; solve [ auto using div_mod, wt_gen0_1, wt_gen_nonzero, wt_gen_divides' ] ].
    destruct b; [ rewrite Tuple.map_id; reflexivity | ].
    apply f_equal.
    admit.
  Qed.

  Record SynthesisReflectiveOptions :=
    {
      add_opts : PipelineOptions;
      sub_opts : PipelineOptions;
      mul_opts : PipelineOptions;
      square_opts : PipelineOptions;
      opp_opts : PipelineOptions;
      carry_opts : PipelineOptions;
    }.

  Local Set Primitive Projections.
  Record eq_package_for {T} (x : T) :=
    {
      output_val : T;
      output_eq :> output_val = x
    }.
  Arguments output_val {_ _} _.
  Arguments output_eq {_ _} _.
  Definition vm_compute_package {T} (x : T) := eq_package_for x.
  Definition cbv_package {T} (x : T) := eq_package_for x.
  Definition lazy_package {T} (x : T) := eq_package_for x.
  Definition by_vm_decide (P : Prop) {Pdec : Decidable P} := P.
  Definition by_reify (T : Type) := T.
  Definition by_transparent_vm_compute_reflexivity (T : Type) := T.
  Ltac handle_compute_packages _ :=
    lazymatch goal with
    | [ |- vm_compute_package ?x ]
      => let x' := (eval vm_compute in x) in
         (exists x'); vm_cast_no_check (eq_refl x')
    | [ |- cbv_package ?x ]
      => eexists; cbv; reflexivity
    | [ |- lazy_package ?x ]
      => eexists; lazy; reflexivity
    | [ |- @by_vm_decide ?P ?Pdec ]
      => abstract (apply (@dec_bool P Pdec); vm_cast_no_check (eq_refl true))
    | [ |- by_reify ?T ]
      => cbv beta delta [by_reify]; do_reify
    | [ |- PipelineEvars ]
      => econstructor; shelve
    | [ |- by_transparent_vm_compute_reflexivity ?T ]
      => vm_compute; reflexivity
    end.

  Definition eq_refl_of_nat {x y : nat} (H : x = y) : x = y
    := match NatUtil.nat_eq_dec x y with
       | left pf => pf
       | right n => match n H with end
       end.

  Definition lift1 {n} (f : Z^n -> Z^n) : interp_flat_type (Tbase TZ^n)%ctype -> interp_flat_type (Tbase TZ^n)%ctype
    := fun x
       => flat_interp_untuple
            (T:=Tbase _)
            (f (flat_interp_tuple x)).

  Definition lift2 {n} (f : Z^n -> Z^n -> Z^n) : interp_flat_type (Tbase TZ^n * Tbase TZ^n)%ctype -> interp_flat_type (Tbase TZ^n)%ctype
    := fun '((x, y) : interp_flat_type _ * interp_flat_type _)
       => flat_interp_untuple
            (T:=Tbase _)
            (f (flat_interp_tuple x) (flat_interp_tuple y)).

  Local Notation v x := (output_val x).
  Local Notation h x := (output_eq x).

  Context (opts : SynthesisReflectiveOptions).

  Local Notation TW := (TWord (Z.log2_up curve.(bitwidth))).

  Definition Compose_rpkg {A B C}
             {fZ gZ}
             (f : { rexpr : Expr (B -> C)%ctype
                  | forall x, Interp rexpr x = fZ x })
             (g : { rexpr : Expr (A -> B)%ctype
                  | forall x, Interp rexpr x = gZ x })
    : { rexpr : Expr (A -> C)%ctype
      | forall x, Interp rexpr x = fZ (gZ x) }
    := exist
         (fun rexpr : Expr (A -> C)%ctype => forall x, Interp rexpr x = fZ (gZ x))
         (proj1_sig f ∘ proj1_sig g)%expr
         (fun x => eq_trans (proj2_sig f _) (f_equal fZ (proj2_sig g x))).

  Record SynthesisSideConditions :=
    {
      sz_nonzero : by_vm_decide (curve.(sz) <> 0%nat);
      sz_small : by_vm_decide (Z.of_nat curve.(sz) <= Z.log2_up curve.(m));

      r' : positive
      := Z.to_pos (2^curve.(bitwidth));
      r : vm_compute_package r';

      m' := OutputType.m;
      m : vm_compute_package m';

      allowable_logsz' := List.map Nat.log2 curve'.(CurveParameters.allowable_bit_widths);
      allowable_logsz : vm_compute_package allowable_logsz';

      limb_widths' := List.map (fun i => Z.log2 (curve.(wt) (S i) / curve.(wt) i)) (seq 0 curve.(sz));
      limb_widths : vm_compute_package limb_widths';

      b_of' := (fun exp => {| lower := 0 ; upper := curve'.(CurveParameters.upper_bound_of_exponent) exp |}%Z);

      (* The definition [bounds_exp] is a tuple-version of the
         limb-widths, which are the [exp] argument in [b_of] above,
         i.e., the approximate base-2 exponent of the bounds on the
         limb in that position. *)
      bounds_exp' : Tuple.tuple Z curve.(sz)
      := Tuple.from_list
           (curve.(sz)) (v limb_widths)
           (eq_refl_of_nat
              (eq_trans
                 (f_equal (@List.length _) (h limb_widths))
                 (eq_trans
                    (map_length _ _)
                    (seq_length _ _))));
      bounds_exp : cbv_package bounds_exp';

      bounds' : Tuple.tuple zrange curve.(sz)
      := Tuple.map (fun e => b_of' e) (v bounds_exp);
      bounds : cbv_package bounds';

      bound1 : zrange
      := {| lower := 0 ; upper := Z.pos (v r)-1 |};

      lgbitwidth' := Z.to_nat (Z.log2_up (List.fold_right Z.max 0 (v limb_widths)));
      lgbitwidth : cbv_package lgbitwidth';

      adjusted_bitwidth' := (Nat.pow 2 (v lgbitwidth))%nat;
      adjusted_bitwidth : cbv_package adjusted_bitwidth';

      input_bounds' : Syntax.interp_flat_type
                        Interpretation.Bounds.interp_base_type
                        (rT TZ)
      := flat_interp_untuple (interp_base_type:=Interpretation.Bounds.interp_base_type) (T:=Tbase _) (v bounds);
      input_bounds : cbv_package input_bounds';

      computed_types_line_up
      : by_transparent_vm_compute_reflexivity
          (SmartFlatTypeMap
             (Interpretation.Bounds.bounds_to_base_type
                (round_up:=Interpretation.Bounds.round_up_to_in_list
                             (v allowable_logsz)))
             (v input_bounds)
           = rT TW);

      zeroZ : vm_compute_package (OutputType.encode curve TZ 0);
      oneZ : vm_compute_package (OutputType.encode curve TZ 1);

      zeroW : vm_compute_package (OutputType.encode curve TW 0);
      oneW : vm_compute_package (OutputType.encode curve TW 1);

      carry : Z^curve.(sz) -> Z^curve.(sz);
      rcarryZ_pkg : by_reify { rexpr : Expr (rT TZ -> rT TZ)%ctype
                             | forall x, Interp rexpr x = lift1 carry x };

      add : Z^curve.(sz) -> Z^curve.(sz) -> Z^curve.(sz);
      raddZ_pkg : by_reify { rexpr : Expr (rT TZ * rT TZ -> rT TZ)%ctype
                           | forall x, Interp rexpr x = lift2 add x };
      raddW_evars : PipelineEvars;
      raddW_side_conditions
      : forall v0,
          { e_final_evar : _
                           & @PipelineSideConditions
                               (v allowable_logsz) (add_opts opts)
                               (rT TZ * rT TZ -> rT TZ)%ctype
                               (v input_bounds, v input_bounds) (v input_bounds)
                               v0
                               (fun xy => lift1 carry (lift2 add xy))
                               e_final_evar
                               raddW_evars
                               (Compose_rpkg rcarryZ_pkg raddZ_pkg) };

      sub : Z^curve.(sz) -> Z^curve.(sz) -> Z^curve.(sz);
      rsubZ_pkg : by_reify { rexpr : Expr (rT TZ * rT TZ -> rT TZ)%ctype
                           | forall x, Interp rexpr x = lift2 sub x };
      rsubW_evars : PipelineEvars;
      rsubW_side_conditions
      : forall v0,
          { e_final_evar : _
                           & @PipelineSideConditions
                               (v allowable_logsz) (sub_opts opts)
                               (rT TZ * rT TZ -> rT TZ)%ctype
                               (v input_bounds, v input_bounds) (v input_bounds)
                               v0
                               (fun xy => lift1 carry (lift2 sub xy))
                               e_final_evar
                               rsubW_evars
                               (Compose_rpkg rcarryZ_pkg rsubZ_pkg) };

      mul : Z^curve.(sz) -> Z^curve.(sz) -> Z^curve.(sz);
      rmulZ_pkg : by_reify { rexpr : Expr (rT TZ * rT TZ -> rT TZ)%ctype
                           | forall x, Interp rexpr x = lift2 mul x };
      rmulW_evars : PipelineEvars;
      rmulW_side_conditions
      : forall v0,
          { e_final_evar : _
                           & @PipelineSideConditions
                               (v allowable_logsz) (mul_opts opts)
                               (rT TZ * rT TZ -> rT TZ)%ctype
                               (v input_bounds, v input_bounds) (v input_bounds)
                               v0
                               (fun xy => lift1 carry (lift2 mul xy))
                               e_final_evar
                               rmulW_evars
                               (Compose_rpkg rcarryZ_pkg rmulZ_pkg) };

      square : Z^curve.(sz) -> Z^curve.(sz);
      rsquareZ_pkg : by_reify { rexpr : Expr (rT TZ -> rT TZ)%ctype
                              | forall x, Interp rexpr x = lift1 square x };
      rsquareW_evars : PipelineEvars;
      rsquareW_side_conditions
      : forall v0,
          { e_final_evar : _
                           & @PipelineSideConditions
                               (v allowable_logsz) (square_opts opts)
                               (rT TZ -> rT TZ)%ctype
                               (v input_bounds) (v input_bounds)
                               v0
                               (fun xy => lift1 carry (lift1 square xy))
                               e_final_evar
                               rsquareW_evars
                               (Compose_rpkg rcarryZ_pkg rsquareZ_pkg) };

      opp : Z^curve.(sz) -> Z^curve.(sz);
      roppZ_pkg : by_reify { rexpr : Expr (rT TZ -> rT TZ)%ctype
                           | forall x, Interp rexpr x = lift1 opp x };
      roppW_evars : PipelineEvars;
      roppW_side_conditions
      : forall v0,
          { e_final_evar : _
              & @PipelineSideConditions
                  (v allowable_logsz) (opp_opts opts)
                  (rT TZ -> rT TZ)%ctype
                  (v input_bounds) (v input_bounds)
                  v0
                  (fun xy => lift1 carry (lift1 opp xy))
                  e_final_evar
                  roppW_evars
                  (Compose_rpkg rcarryZ_pkg roppZ_pkg) };

    }.

  Context (side_conditions : SynthesisSideConditions).
  Local Notation v' x := (output_val (x side_conditions)).
  Local Notation v0 x := (x side_conditions).

  Goal SynthesisOutput curve.
    simple refine (let transform1 := (fun e => eq_rect _ (fun t => Expr (t -> t)) e _ (v0 computed_types_line_up)) in
                   let transform2 := (fun e => eq_rect _ (fun t => Expr (t * t -> t)) e _ (v0 computed_types_line_up)) in
                   {|
                     OutputType.zeroZ := v' zeroZ;
                     OutputType.oneZ := v' oneZ;
                     OutputType.zeroW := v' zeroW;
                     OutputType.oneW := v' oneW;
                     OutputType.addZ := proj1_sig (v0 raddZ_pkg);
                     OutputType.subZ := proj1_sig (v0 rsubZ_pkg);
                     OutputType.carry_mulZ := (proj1_sig (v0 rcarryZ_pkg) ∘ proj1_sig (v0 rmulZ_pkg))%expr;
                     OutputType.oppZ := proj1_sig (v0 roppZ_pkg);
                     OutputType.carry_squareZ := (proj1_sig (v0 rcarryZ_pkg) ∘ proj1_sig (v0 rsquareZ_pkg))%expr;
                     OutputType.carryZ := proj1_sig (v0 rcarryZ_pkg);

                     OutputType.carry_addW := transform2 (let ev := raddW_evars side_conditions in e_final_newtype);
                     OutputType.carry_subW := transform2 (let ev := rsubW_evars side_conditions in e_final_newtype);
                     OutputType.carry_mulW := transform2 (let ev := rmulW_evars side_conditions in e_final_newtype);
                     OutputType.carry_oppW := transform1 (let ev := roppW_evars side_conditions in e_final_newtype);
                     OutputType.carry_squareW := transform1 (let ev := rsquareW_evars side_conditions in e_final_newtype);

                     OutputType.encodeZ_correct := encode_correct _ (v0 sz_nonzero) (v0 sz_small);
                     OutputType.encodeW_correct := encode_correct _ (v0 sz_nonzero) (v0 sz_small);
                   |}).
    all: subst transform1 transform2.
    all: repeat first [ match goal with
                        | [ |- ?G ] => has_evar G; fail
                        | _ => reflexivity
                        end
                      | apply output_eq
                      | rewrite output_eq
                      | progress cbv beta zeta ].
    Show Proof.
    pose .
    refine (let k :=  e in _).
    lazymatch goal with
    | [ e := _ : Expr ?T |- Expr ?T' ]
      => assert (T = T')
    end.
    { clear.

      repeat rewrite !output_eq.
      destruct (v0 limb_widths); subst; simpl.
      rewrite SmartFlatTypeMap_Pair.
      cbn [fst snd].
      f_equal; [ f_equal | ].
      { Set Printing Implicit.

      SearchAbout Tuple.from_list List.map.
      SearchAbout Tuple.map Tuple.from_list.
    cbv [SmartFlatTypeMap] in e.
    Show Proof.
    Focus 13.
    Set Printing All.


    Print SynthesisOutput.
             oneZ
    Check (fun v0 => ).



Ltac pose_local_feZ sz feZ :=
  pose_term_with
    ltac:(fun _ => constr:(tuple Z sz))
           feZ.

Ltac pose_feW sz lgbitwidth feW :=
  cache_term_with_type_by
    Type
    ltac:(let v := eval cbv [lgbitwidth] in (tuple (wordT lgbitwidth) sz) in exact v)
           feW.
Ltac pose_feW_bounded feW bounds feW_bounded :=
  cache_term_with_type_by
    (feW -> Prop)
    ltac:(let v := eval cbv [bounds] in (fun w : feW => is_bounded_by None bounds (map wordToZ w)) in exact_no_check v)
           feW_bounded.
Ltac pose_feBW sz adjusted_bitwidth' bounds feBW :=
  cache_term_with_type_by
    Type
    ltac:(let v := eval cbv [adjusted_bitwidth' bounds] in (BoundedWord sz adjusted_bitwidth' bounds) in exact v)
           feBW.

  Record SynthesisPreOutput :=
    {
      add : Z Expr (rT * rT -> rT); (* does not include carry *)
      sub : Expr (rT * rT -> rT); (* does not include carry *)
      mul : Expr (rT * rT -> rT); (* includes carry *)
      square : Expr (rT -> rT); (* includes carry *)
      opp : Expr (rT -> rT); (* does not include carry *)
      carry : Expr (rT -> rT);
      carry_add : Expr (rT * rT -> rT)
      := (carry ∘ add)%expr;
      carry_sub : Expr (rT * rT -> rT)
      := (carry ∘ sub)%expr;
      carry_opp : Expr (rT -> rT)
      := (carry ∘ opp)%expr;

      P : T' -> Prop;

      encode_valid : forall v, P (Interp (encode v) tt);

      zero_correct : zero = encode 0%F; (* which equality to use here? *)
      one_correct : one = encode 1%F; (* which equality to use here? *)

      opp_valid : forall x, P x -> P (Interp carry_opp x);
      add_valid : forall x y, P x -> P y -> P (Interp carry_add (x, y));
      sub_valid : forall x y, P x -> P y -> P (Interp carry_sub (x, y));
      mul_valid : forall x y, P x -> P y -> P (Interp mul (x, y));
      square_correct : forall x, P x -> Interp square x = Interp mul (x, x);
    }.

  Definition FinalizeOutput (v : SynthesisPreOutput) : SynthesisOutput curve.
  Proof.
    simple refine (let ring_goal : _ /\ _ /\ _ := _ in _); [ shelve.. | | ]; cycle 1.
    simple refine {|
             OutputType.zero := v.(zero);
             OutputType.one := v.(one);
             OutputType.add := v.(add);
             OutputType.sub := v.(sub);
             OutputType.mul := v.(mul);
             OutputType.opp := v.(opp);
             OutputType.carry := v.(carry);
             OutputType.square := v.(square);

             OutputType.zero_correct := v.(zero_correct);
             OutputType.one_correct := v.(one_correct);
             OutputType.encode_valid := v.(encode_valid);
             OutputType.add_valid := v.(add_valid);
             OutputType.sub_valid := v.(sub_valid);
             OutputType.mul_valid := v.(mul_valid);
             OutputType.opp_valid := v.(opp_valid);
             OutputType.square_correct := v.(square_correct);

             OutputType.ring := proj1 ring_goal;
             OutputType.encode_homomorphism := proj1 (proj2 ring_goal);
             OutputType.decode_homomorphism := proj2 (proj2 ring_goal);
           |}.
    { intro x; cbv [decode encode Interp interp].
      lazymatch goal with
      | [ |- context G[flat_interp_untuple (Tuple.map ?f ?x)] ]
          let G' := context[tuple_map f x]
      SearchAbout interpf SmartPairf.
    constructor.
