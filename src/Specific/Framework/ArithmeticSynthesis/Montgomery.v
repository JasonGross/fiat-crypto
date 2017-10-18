Require Import Coq.micromega.Lia.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Definition.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Proofs.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Crypto.Arithmetic.Saturated.MontgomeryAPI.
Require Import Crypto.Arithmetic.Saturated.UniformWeight.
Require Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Reify.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.Tuple.
Require Import Crypto.Arithmetic.Compiled.Core.
Require Import Crypto.Arithmetic.Compiled.Saturated.Montgomery.
Require Import Crypto.Util.Sigma.Lift.
Require Import Coq.ZArith.BinInt.
Require Import Coq.PArith.BinPos.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ZUtil.ModInv.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Arithmetic.Saturated.UniformWeightInstances.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.HelperTactics.
Require Import Crypto.Util.SideConditions.CorePackages.
Require Import Crypto.Util.SideConditions.ModInvPackage.
Require Import Crypto.Util.SideConditions.AdmitPackage.
Require Import Crypto.Util.SideConditions.ReductionPackages.
Require Import Crypto.Util.Tactics.CacheTerm.
Local Open Scope Z_scope.
Local Infix "^" := Tuple.tuple : type_scope.

Local Set Implicit Arguments.

Local Existing Instance Tuple.dec_eq'.

Local Definition sig_by_eq {A P} (x : { a : A | P a }) (a : A) (H : a = proj1_sig x)
  : { a : A | P a }.
Proof.
  exists a; subst; exact (proj2_sig x).
Defined.

Section with_args.
  Context (wt : nat -> Z)
          (r : positive)
          (sz : nat)
          (m : positive)
          (m_enc : Z^sz)
          (r' : Z)
          (r'_correct : ((Z.pos r * r') mod (Z.pos m) = 1)%Z)
          (m' : Z)
          (m'_correct : ((Z.pos m * m') mod (Z.pos r) = (-1) mod Z.pos r)%Z)
          (m_enc_correct_montgomery : Z.pos m = MontgomeryAPI.eval (n:=sz) (Z.pos r) m_enc)
          (r'_pow_correct : ((r' ^ Z.of_nat sz * Z.pos r ^ Z.of_nat sz) mod MontgomeryAPI.eval (n:=sz) (Z.pos r) m_enc = 1)%Z)
          (* computable *)
          (r_big : Z.pos r > 1)
          (m_big : 1 < Z.pos m)
          (m_enc_small : small (Z.pos r) m_enc)
          (map_m_enc : Tuple.map (Z.land (Z.pos r - 1)) m_enc = m_enc).

  Local Ltac t_fin :=
    repeat match goal with
           | _ => assumption
           | [ |- ?x = ?x ] => reflexivity
           | [ |- and _ _ ] => split
           | [ |- (0 <= MontgomeryAPI.eval (Z.pos r) _)%Z ] => apply MontgomeryAPI.eval_small
           | _ => rewrite <- !m_enc_correct_montgomery
           | _ => rewrite !r'_correct
           | _ => rewrite !Z.mod_1_l by assumption; reflexivity
           | _ => rewrite !(Z.mul_comm m' (Z.pos m))
           | _ => lia
           end.


  Local Definition mul'_gen
    : { f:Z^sz -> Z^sz -> Z^sz
      | forall (A B : Z^sz),
          small (Z.pos r) A -> small (Z.pos r) B ->
          let eval := MontgomeryAPI.eval (Z.pos r) in
          (small (Z.pos r) (f A B)
           /\ (eval B < eval m_enc -> 0 <= eval (f A B) < eval m_enc)
           /\ (eval (f A B) mod Z.pos m
               = (eval A * eval B * r'^(Z.of_nat sz)) mod Z.pos m))%Z
      }.
  Proof.
    exists (fun A B => redc (r:=r)(R_numlimbs:=sz) m_enc A B m').
    abstract (
        intros;
        split; [ | split ];
        [ apply small_redc with (ri:=r') | apply redc_bound_N with (ri:=r') | rewrite !m_enc_correct_montgomery; apply redc_mod_N ];
        t_fin
      ).
  Defined.

  Import ModularArithmetic.

  Definition montgomery_to_F_gen (v : Z) : F m
    := (F.of_Z m v * F.of_Z m (r'^Z.of_nat sz)%Z)%F.

  Definition montgomery_of_F_gen (v : F m) : Z
    := F.to_Z (v * F.of_Z m (r^Z.of_nat sz))%F.

  Lemma montgomery_to_F_of_F_gen v
    : montgomery_to_F_gen (montgomery_of_F_gen v) = v.
  Proof.
    cbv [montgomery_to_F_gen montgomery_of_F_gen].
    rewrite F.of_Z_to_Z, <- (F.of_Z_to_Z v), F.eq_to_Z_iff.
    autorewrite with pull_FofZ.
    rewrite <- Z.mul_assoc, !F.to_Z_of_Z, (Z.mul_comm (Z.pos r ^ _)), <- Z.pow_mul_l.
    push_Zmod.
    rewrite Z.pow_mul_l, m_enc_correct_montgomery, r'_pow_correct, <- m_enc_correct_montgomery, Z.mul_1_r.
    pull_Zmod.
    reflexivity.
  Qed.

  Lemma montgomery_of_F_gen_bounded (v : F m)
    : 0 <= montgomery_of_F_gen v < Z.pos r ^ Z.of_nat sz.
  Proof.
    cbv [montgomery_of_F_gen].
    rewrite <- F.mod_to_Z.
    split; [ | etransitivity ];
      [ apply Z.mod_pos_bound; lia.. | ].
    rewrite m_enc_correct_montgomery.
    apply MontgomeryAPI.eval_small; [ lia | ].
    apply m_enc_small.
  Qed.

  Local Definition mul_ext_gen
    : { f:Z^sz -> Z^sz -> Z^sz
      | let eval := MontgomeryAPI.eval (Z.pos r) in
        (forall (A : Z^sz) (_ : small (Z.pos r) A)
                (B : Z^sz) (_ : small (Z.pos r) B),
            montgomery_to_F_gen (eval (f A B))
            = (montgomery_to_F_gen (eval A) * montgomery_to_F_gen (eval B))%F)
        /\ (forall (A : Z^sz) (_ : small (Z.pos r) A)
                   (B : Z^sz) (_ : small (Z.pos r) B),
               (eval B < eval m_enc -> 0 <= eval (f A B) < eval m_enc)%Z)
        /\ (forall (A : Z^sz) (_ : small (Z.pos r) A)
                   (B : Z^sz) (_ : small (Z.pos r) B),
               small (Z.pos r) (f A B)) }.
  Proof.
    exists (proj1_sig mul'_gen).
    abstract (
        cbv zeta; intros; repeat apply conj; intros A Asm B Bsm;
        pose proof (proj2_sig mul'_gen A B Asm Bsm) as H;
        cbv zeta in *;
        try solve [ destruct_head'_and; assumption ];
        rewrite ModularArithmeticTheorems.F.eq_of_Z_iff in H;
        unfold montgomery_to_F_gen;
        destruct H as [H1 [H2 H3]]; trivial;
        rewrite H3;
        rewrite <- !ModularArithmeticTheorems.F.of_Z_mul;
        f_equal; nia
      ).
  Defined.

  Local Definition add_ext_gen
    : { f:Z^sz -> Z^sz -> Z^sz
      | let eval := MontgomeryAPI.eval (Z.pos r) in
        ((forall (A : Z^sz) (_ : small (Z.pos r) A)
                 (B : Z^sz) (_ : small (Z.pos r) B),
             (eval A < eval m_enc
              -> eval B < eval m_enc
              -> montgomery_to_F_gen (eval (f A B))
                 = (montgomery_to_F_gen (eval A) + montgomery_to_F_gen (eval B))%F))
         /\ (forall (A : Z^sz) (_ : small (Z.pos r) A)
                    (B : Z^sz) (_ : small (Z.pos r) B),
                (eval A < eval m_enc
                 -> eval B < eval m_enc
                 -> 0 <= eval (f A B) < eval m_enc))
         /\ (forall (A : Z^sz) (_ : small (Z.pos r) A)
                    (B : Z^sz) (_ : small (Z.pos r) B),
                (eval A < eval m_enc
                 -> eval B < eval m_enc
                 -> small (Z.pos r) (f A B))))%Z }.
  Proof.
    exists (fun A B => add (r:=r)(R_numlimbs:=sz) m_enc A B).
    abstract (
        cbv zeta; repeat apply conj; intros;
        unfold montgomery_to_F_gen; rewrite <- ?ModularArithmeticTheorems.F.of_Z_mul, <- ?ModularArithmeticTheorems.F.of_Z_add;
        rewrite <- ?Z.mul_add_distr_r;
        [ rewrite <- ModularArithmeticTheorems.F.eq_of_Z_iff, m_enc_correct_montgomery; push_Zmod; rewrite eval_add_mod_N; pull_Zmod
        | apply add_bound
        | apply small_add ];
        t_fin
      ).
  Defined.

  Local Definition sub_ext_gen
    : { f:Z^sz -> Z^sz -> Z^sz
      | let eval := MontgomeryAPI.eval (Z.pos r) in
        ((forall (A : Z^sz) (_ : small (Z.pos r) A)
                 (B : Z^sz) (_ : small (Z.pos r) B),
             (eval A < eval m_enc
              -> eval B < eval m_enc
              -> montgomery_to_F_gen (eval (f A B))
                 = (montgomery_to_F_gen (eval A) - montgomery_to_F_gen (eval B))%F))
         /\ (forall (A : Z^sz) (_ : small (Z.pos r) A)
                    (B : Z^sz) (_ : small (Z.pos r) B),
                (eval A < eval m_enc
                 -> eval B < eval m_enc
                 -> 0 <= eval (f A B) < eval m_enc))
         /\ (forall (A : Z^sz) (_ : small (Z.pos r) A)
                    (B : Z^sz) (_ : small (Z.pos r) B),
                (eval A < eval m_enc
                 -> eval B < eval m_enc
                 -> small (Z.pos r) (f A B))))%Z }.
  Proof.
    exists (fun A B => sub (r:=r) (R_numlimbs:=sz) m_enc A B).
    abstract (
        cbv zeta; intros; repeat apply conj; intros;
        unfold montgomery_to_F_gen; rewrite <- ?ModularArithmeticTheorems.F.of_Z_mul, <- ?ModularArithmeticTheorems.F.of_Z_sub;
        rewrite <- ?Z.mul_sub_distr_r;
        [ rewrite <- ModularArithmeticTheorems.F.eq_of_Z_iff, m_enc_correct_montgomery; push_Zmod; rewrite eval_sub_mod_N; pull_Zmod
        | apply sub_bound
        | apply small_sub ];
        t_fin
      ).
  Defined.

  Local Definition opp_ext_gen
    : { f:Z^sz -> Z^sz
      | let eval := MontgomeryAPI.eval (Z.pos r) in
        ((forall (A : Z^sz) (_ : small (Z.pos r) A),
             (eval A < eval m_enc
              -> montgomery_to_F_gen (eval (f A))
                 = (F.opp (montgomery_to_F_gen (eval A)))%F))
         /\ (forall (A : Z^sz) (_ : small (Z.pos r) A),
                (eval A < eval m_enc
                 -> 0 <= eval (f A) < eval m_enc))
         /\ (forall (A : Z^sz) (_ : small (Z.pos r) A),
                (eval A < eval m_enc
                 -> small (Z.pos r) (f A))))%Z }.
  Proof.
    exists (fun A => opp (r:=r) (R_numlimbs:=sz) m_enc A).
    abstract (
        cbv zeta; intros; repeat apply conj; intros;
        unfold montgomery_to_F_gen; rewrite <- ?ModularArithmeticTheorems.F.of_Z_mul, <- ?F_of_Z_opp;
        rewrite <- ?Z.mul_opp_l;
        [ rewrite <- ModularArithmeticTheorems.F.eq_of_Z_iff, m_enc_correct_montgomery; push_Zmod; rewrite eval_opp_mod_N; pull_Zmod
        | apply opp_bound
        | apply small_opp ];
        t_fin
      ).
  Defined.

  (* This is kind-of stupid, but we add it for consistency *)
  Local Definition carry_ext_gen
    : { f:Z^sz -> Z^sz
      | let eval := MontgomeryAPI.eval (Z.pos r) in
        ((forall (A : Z^sz) (_ : small (Z.pos r) A),
             (eval A < eval m_enc
              -> montgomery_to_F_gen (eval (f A))
                 = montgomery_to_F_gen (eval A))))
         /\ (forall (A : Z^sz) (_ : small (Z.pos r) A),
                (eval A < eval m_enc
                 -> 0 <= eval (f A) < eval m_enc)
         /\ (forall (A : Z^sz) (_ : small (Z.pos r) A),
                (eval A < eval m_enc
                 -> small (Z.pos r) (f A))))%Z }.
  Proof.
    exists (fun A => A).
    abstract (
        cbv zeta; repeat (eauto || apply conj || intros);
        apply MontgomeryAPI.eval_small; auto; lia
      ).
  Defined.

  Local Definition nonzero_ext_gen
    : { f:Z^sz -> Z
      | let eval := MontgomeryAPI.eval (Z.pos r) in
        forall (A : Z^sz) (_ : small (Z.pos r) A),
          (eval A < eval m_enc
           -> f A = 0 <-> (montgomery_to_F_gen (eval A) = F.of_Z m 0))%Z }.
  Proof.
    exists (fun A => nonzero (R_numlimbs:=sz) A).
    abstract (
        intros eval A H **; rewrite (@eval_nonzero r) by (eassumption || reflexivity);
        subst eval;
        unfold montgomery_to_F_gen, uweight in *; rewrite <- ?ModularArithmeticTheorems.F.of_Z_mul;
        rewrite <- ModularArithmeticTheorems.F.eq_of_Z_iff, m_enc_correct_montgomery;
        let H := fresh in
        split; intro H;
        [ rewrite H; autorewrite with zsimplify_const; reflexivity
        | cut ((MontgomeryAPI.eval (Z.pos r) A * (r' ^ Z.of_nat sz * Z.pos r ^ Z.of_nat sz)) mod MontgomeryAPI.eval (n:=sz) (Z.pos r) m_enc = 0)%Z;
          [ rewrite Z.mul_mod, r'_pow_correct; autorewrite with zsimplify_const; pull_Zmod; [ | t_fin ];
            rewrite Z.mod_small; [ trivial | split; try assumption; apply MontgomeryAPI.eval_small; try assumption; lia ]
          | rewrite Z.mul_assoc, Z.mul_mod, H by t_fin; autorewrite with zsimplify_const; reflexivity ] ]
      ).
  Defined.
End with_args.

Local Definition for_assumptions
  := (mul_ext_gen, add_ext_gen, sub_ext_gen, opp_ext_gen, nonzero_ext_gen).

Print Assumptions for_assumptions.

Section with_curves.
  Import CurveParameters.CurveParameters.
  Context (curve : CurveParameters)
          (curve_sc : CurveParameterBaseSideConditions curve).

  Local Notation modinv_fuel := curve.(modinv_fuel).
  Local Notation m := curve.(m).
  Local Notation r := curve.(r).
  Local Notation base := curve.(base).
  Local Notation sz := curve.(sz).
  Local Notation s := curve.(s).
  Local Notation c := curve.(c).
  Local Notation carry_chains := curve.(carry_chains).
  Local Notation coef := curve.(coef).
  Local Notation mul_code := curve.(mul_code).
  Local Notation square_code := curve.(square_code).
  Local Notation sz_nonzero := curve_sc.(sz_nonzero).
  Local Notation sz2_nonzero := curve_sc.(sz2_nonzero).
  Local Notation s_nonzero := curve_sc.(s_nonzero).
  Local Notation base_pos := curve_sc.(base_pos).
  Local Notation sz_le_log2_m := curve_sc.(sz_le_log2_m).
  Local Notation wt := curve.(wt).
  Local Notation sz2 := curve.(sz2).
  Local Notation half_sz := curve.(half_sz).
  Local Notation sqrt_s := curve.(sqrt_s).
  Local Notation bitwidth := curve.(bitwidth).
  Local Notation m_enc := curve.(m_enc).
  Local Notation wt0_1 := curve_sc.(wt0_1).
  Local Notation wt_divides' := curve_sc.(wt_divides').
  Local Notation wt_nonzero := curve_sc.(wt_nonzero).
  Local Notation coef_mod := curve_sc.(coef_mod).
  Local Notation m_correct := curve_sc.(m_correct).
  Local Notation wt_divides_chains := curve_sc.(wt_divides_chains).
  Local Notation sqrt_s_nonzero := curve_sc.(sqrt_s_nonzero).
  Local Notation sqrt_s_correct := curve_sc.(sqrt_s_correct).
  Local Notation fst_nat_divmod_sz_nonzero := curve_sc.(fst_nat_divmod_sz_nonzero).
  Local Notation wt_divides := curve_sc.(wt_divides).
  Local Notation wt_pos := curve_sc.(wt_pos).
  Local Notation wt_multiples := curve_sc.(wt_multiples).
  Local Notation c_small := curve_sc.(c_small).
  Local Notation m_enc_bounded := curve_sc.(m_enc_bounded).
  Local Notation m_correct_wt := curve_sc.(m_correct_wt).
  Local Notation m_enc_correct := curve_sc.(m_enc_correct).

  Local Notation exprT sz n szR :=
    (((Tbase TZ^sz%nat)^n%nat -> Tbase TZ^szR%nat)%ctype)
      (only parsing).

  Let unoption_Expr_evar_package {sz szR}
      n
      (v : option
             (Expr
                (SmartMap.lift_flat_type
                   Util.unextend_base_type
                   ((Tbase Syntax.TZ ^ sz)^n)%ctype ->
                 SmartMap.lift_flat_type
                   Util.unextend_base_type
                   (Tbase Syntax.TZ ^ szR))))
    := cast_evar_package
         (invert_Some v)
         (Expr (exprT sz n szR)).

  Import Crypto.Spec.ModularArithmetic.

  Record CurveParameterMontgomeryBaseSideConditions :=
    { m' : modinv_evar_package modinv_fuel (-Z.pos m) (Z.pos r) (* (-m)⁻¹ mod r *);
      r' : modinv_evar_package modinv_fuel (Z.pos r) (Z.pos m) (* r⁻¹ mod m *);

      r'_correct : (Z.pos r * val r') mod (Z.pos m) = 1
      := evar_package_pf r';

      m_enc_correct_montgomery' : vm_decide_package _;
      m_enc_correct_montgomery : Z.pos m = MontgomeryAPI.eval (n:=sz) (Z.pos r) m_enc
      := m_enc_correct_montgomery';

      r'_pow_correct' : vm_decide_package _;
      r'_pow_correct : (val r' ^ Z.of_nat sz * Z.pos r ^ Z.of_nat sz) mod MontgomeryAPI.eval (n:=sz) (Z.pos r) m_enc = 1
      := r'_pow_correct';

      montgomery_to_F v := F.mul (F.of_Z m v) (F.of_Z m (val r'^Z.of_nat sz)%Z);
      montgomery_of_F v := F.to_Z (v * F.of_Z m (r^Z.of_nat sz))%F;

      r_big' : vm_decide_package _;
      r_big : Z.pos r > 1 := r_big';

      m_big' : vm_decide_package _;
      m_big : 1 < Z.pos m := m_big';

      m_enc_small' : vm_decide_package _;
      m_enc_small : small (n:=sz) (Z.pos r) m_enc
      := @dec_bool _ _ m_enc_small';

      map_m_enc' : vm_decide_package _;
      map_m_enc : Tuple.map (n:=sz) (Z.land (Z.pos r - 1)) m_enc = m_enc
      := @dec_bool _ _ map_m_enc';
    }.

  Context (curve_msc : CurveParameterMontgomeryBaseSideConditions).

  Local Notation m'' := (val curve_msc.(m')).
  Local Notation r'' := (val curve_msc.(r')).
  Local Notation r'_correct' := curve_msc.(r'_correct).
  Local Notation m_enc_correct_montgomery'' := curve_msc.(m_enc_correct_montgomery).
  Local Notation r'_pow_correct'' := curve_msc.(r'_pow_correct).
  Local Notation r_big'' := curve_msc.(r_big).
  Local Notation m_big'' := curve_msc.(m_big).
  Local Notation m_enc_small'' := curve_msc.(m_enc_small).
  Local Notation map_m_enc'' := curve_msc.(map_m_enc).
  Local Notation montgomery_to_F' := curve_msc.(montgomery_to_F).
  Local Notation montgomery_of_F' := curve_msc.(montgomery_of_F).

  Lemma montgomery_to_F_of_F v
    : montgomery_to_F' (montgomery_of_F' v) = v.
  Proof.
    eapply montgomery_to_F_of_F_gen;
      eauto using m_enc_correct_montgomery, r'_pow_correct.
  Qed.

  Lemma montgomery_of_F_bounded (v : F m)
    : 0 <= montgomery_of_F' v < Z.pos r ^ Z.of_nat sz.
  Proof.
    eapply montgomery_of_F_gen_bounded;
      eauto using m_enc_correct_montgomery, r'_pow_correct, r_big, m_big, m_enc_small.
  Qed.

  Lemma m'_correct
    : (Z.pos m * m'') mod (Z.pos r) = (-1) mod Z.pos r.
  Proof.
    pose proof (evar_package_pf curve_msc.(m')) as H; cbv beta in *.
    generalize dependent m''; generalize m; generalize r; clear; intros r m m' H;
      cbv [raw_evar_package] in *.
    destruct (Z.eq_dec (Z.pos r) 1).
    { destruct r as [[r|r|]|r|]; try congruence; try discriminate.
      rewrite !Z.mod_1_r; reflexivity. }
    change (-1) with (-(1)).
    rewrite Z.mul_opp_l in H.
    rewrite !Zdiv.Z_mod_nz_opp_full in *;
      rewrite ?Z.mod_1_l by lia; try lia;
        intro H';
        rewrite Zdiv.Z_mod_zero_opp_full in H by assumption; congruence.
  Qed.

  Local Notation Fencode := (@Positional.Fencode wt sz m (@modulo_cps) (@div_cps)).

  Let encode_const : F m -> Expr (Unit -> (Tbase TZ)^sz)%ctype
    := fun v var
       => Abs
            (fun _
             => SmartMap.SmartPairf
                  (flat_interp_untuple
                     (T:=Tbase _)
                     (Tuple.map
                        (fun v => Op (OpConst v) TT)
                        (Fencode v)))).

  Local Notation admit := (match AdmitAxiom.proof_admitted with end).

  Record montgomery_side_conditions :=
    {
      not_freeze : vm_decide_package (curve.(freeze) = false);
      tight_is_limb_width' : vm_decide_package _;
      tight_is_limb_width : curve.(bounds_tight) = curve.(bounds_limb_widths)
      := tight_is_limb_width';
      loose_is_limb_width' : vm_decide_package _;
      loose_is_limb_width : curve.(bounds_loose) = curve.(bounds_limb_widths)
      := loose_is_limb_width';
      limb_width_is_bitwidth' : vm_decide_package _;
      limb_width_is_bitwidth : curve.(bounds_limb_widths) = curve.(bounds_bitwidths)
      := limb_width_is_bitwidth';

      vm_compiled_preadd : vm_compute_evar_package (Compiler.fill_first_of_pair_tupleZ (compiled_preadd r sz) m_enc);
      vm_compiled_presub : vm_compute_evar_package (Compiler.fill_first_of_pair_tupleZ (compiled_presub r sz) m_enc);
      vm_compiled_preopp : vm_compute_evar_package (Compiler.fill_first_of_pair_tupleZ (compiled_preopp r sz) m_enc);
      vm_compiled_prenonzero : vm_compute_evar_package (compiled_prenonzero sz);
      vm_compiled_premul : vm_compute_evar_package (Compiler.fill_first_of_pair_tupleZ (compiled_preredc' r sz sz m'') m_enc);

      evalF := montgomery_to_F';
      evalZ := MontgomeryAPI.eval (n:=sz) (Z.pos r);
      evalE := flat_interp_tuple (interp_base_type:=interp_base_type) (n:=sz) (T:=Tbase TZ);
      preeval x := evalZ (evalE x);
      eval x := evalF (preeval x);

      zeroZ : vm_compute_evar_package_vm_small (encode_const 0%F);
      oneZ : vm_compute_evar_package_vm_small (encode_const 1%F);
      addZ : unoption_Expr_evar_package 2 (val vm_compiled_preadd);
      subZ : unoption_Expr_evar_package 2 (val vm_compiled_presub);
      oppZ : unoption_Expr_evar_package 1 (val vm_compiled_preopp);
      nonzeroZ : unoption_Expr_evar_package 1 (val vm_compiled_prenonzero);
      mulZ : unoption_Expr_evar_package 2 (val vm_compiled_premul);
      val_squareZ : Expr (exprT sz 1 sz)
      := fun var => Abs (fun x => invert_Abs (val mulZ var) (x, x));

      interp_addZ
      : admit_package
          (forall x y, evalE (Interp (val addZ) (x, y))
                       = Compiler.do_apply (add_patterned r sz (m_enc, (evalE x, evalE y))))
      := admit;
      interp_subZ
      : admit_package
          (forall x y, evalE (Interp (val subZ) (x, y))
                       = Compiler.do_apply (sub_patterned r sz (m_enc, (evalE x, evalE y))))
      := admit;
      interp_oppZ
      : admit_package
          (forall x, evalE (Interp (val oppZ) x)
                     = Compiler.do_apply (opp_patterned r sz (m_enc, (evalE x))))
      := admit;
      interp_mulZ
      : admit_package
          (forall x y, evalE (Interp (val mulZ) (x, y))
                       = Compiler.do_apply (redc_patterned r sz sz m'' (m_enc, (evalE x, evalE y))))
      := admit;
      interp_nonzeroZ
      : admit_package
          (forall x, Interp (val nonzeroZ) x
                     = Compiler.do_apply (nonzero_patterned sz (evalE x)))
      := admit;

    }.

  Context (curve_scd : montgomery_side_conditions).

  Local Notation evalZ' := curve_scd.(evalZ).
  Local Notation evalE' := curve_scd.(evalE).
  Local Notation evalF' := curve_scd.(evalF).
  Local Notation eval' := curve_scd.(eval).
  Local Notation preeval' := curve_scd.(preeval).
  (*Local Notation zeroZ' := (val curve_scd.(zeroZ)).
  Local Notation oneZ' := (val curve_scd.(oneZ)).*)
  Local Notation addZ' := (val curve_scd.(addZ)).
  Local Notation subZ' := (val curve_scd.(subZ)).
  Local Notation oppZ' := (val curve_scd.(oppZ)).
  Local Notation mulZ' := (val curve_scd.(mulZ)).
  Local Notation nonzeroZ' := (val curve_scd.(nonzeroZ)).
  (*Local Notation freezeZ' := (val curve_scd.(freezeZ)).*)
  Local Notation squareZ' := curve_scd.(val_squareZ).

  (*Lemma eval_zeroZ
    : evalZ' zeroZ' = 0%F.
  Proof. rewrite evar_package_pf_eq; apply proj2_sig. Qed.
  Lemma eval_oneZ
    : evalZ' oneZ' = 1%F.
  Proof. rewrite evar_package_pf_eq; apply proj2_sig. Qed.*)

  Local Ltac eval_t_whenever :=
    repeat first [ progress cbn in *
                 | progress intros
                 | progress cbv [eval' preeval' evalZ' LetIn.Let_In evalF' montgomery_to_F montgomery_to_F_gen] in *
                 | progress subst
                 | progress destruct_head'_prod
                 | progress destruct_head'_and
                 | progress destruct_head'_sig
                 | match goal with
                   | [ H : False |- _ ] => exfalso; assumption
                   | [ |- context[Interp (val (addZ _))] ] => rewrite interp_addZ
                   | [ |- context[Interp (val (subZ _))] ] => rewrite interp_subZ
                   | [ |- context[Interp (val (oppZ _))] ] => rewrite interp_oppZ
                   | [ |- context[Interp (val (mulZ _))] ] => rewrite interp_mulZ
                   | [ |- context[Interp (val (nonzeroZ _))] ] => rewrite interp_nonzeroZ
                   | [ |- context[add_patterned] ] => rewrite add_patterned_correct
                   | [ |- context[sub_patterned] ] => rewrite sub_patterned_correct
                   | [ |- context[redc_patterned] ] => rewrite redc_patterned_correct
                   | [ |- context[opp_patterned] ] => rewrite opp_patterned_correct
                   | [ |- context[nonzero_patterned] ] => rewrite nonzero_patterned_correct
                   end
                 | solve [ eauto 12 ] ].

  Local Ltac eval_t_pose :=
    pose proof wt_nonzero;
    pose proof sz_nonzero;
    pose proof sz2_nonzero;
    pose proof wt0_1;
    pose proof coef_mod;
    pose proof div_mod;
    pose proof s_nonzero;
    pose proof m_correct;
    pose proof wt_divides';
    pose proof wt_divides_chains;
    pose proof wt_divides;
    pose proof wt_pos;
    pose proof wt_multiples;
    pose proof c_small;
    pose proof m_enc_bounded;
    pose proof div_correct; pose proof modulo_correct;
    pose proof m'_correct;
    pose proof r'_correct';
    pose proof m_enc_correct_montgomery'';
    pose proof r'_pow_correct'';
    pose proof r_big'';
    pose proof m_big'';
    pose proof m_enc_small'';
    pose proof map_m_enc''.
  (*Local Ltac eval_t_pose_freeze :=
    pose proof m_correct_wt;
    pose proof m_enc_correct.*)

  Local Ltac eval_t :=
    eval_t_pose;
    eval_t_whenever.

  Lemma addZ_gen
    : forall ab,
      (small (Z.pos r) (evalE' (fst ab))
       -> small (Z.pos r) (evalE' (snd ab))
       -> preeval' (fst ab) < evalZ' m_enc
       -> preeval' (snd ab) < evalZ' m_enc
       -> eval' (Interp addZ' ab) = (eval' (fst ab) + eval' (snd ab))%F)
      /\ (small (Z.pos r) (evalE' (fst ab))
          -> small (Z.pos r) (evalE' (snd ab))
          -> preeval' (fst ab) < evalZ' m_enc
          -> preeval' (snd ab) < evalZ' m_enc
          -> 0 <= preeval' (Interp addZ' ab) < evalZ' m_enc)
      /\ (small (Z.pos r) (evalE' (fst ab))
          -> small (Z.pos r) (evalE' (snd ab))
          -> preeval' (fst ab) < evalZ' m_enc
          -> preeval' (snd ab) < evalZ' m_enc
          -> small (Z.pos r) (evalE' (Interp addZ' ab))).
  Proof.
    pose proof (proj2_sig (@add_ext_gen r sz m m_enc r'' m_enc_correct_montgomery'' r_big'' m_big'' m_enc_small'')) as H.
    cbv [add_ext_gen proj1_sig] in H.
    eval_t.
  Qed.

  Definition eval_addZ ab := proj1 (addZ_gen ab).
  Definition bounded_eval_addZ ab := proj2 (addZ_gen ab).

  Lemma subZ_gen
    : forall ab,
      (small (Z.pos r) (evalE' (fst ab))
       -> small (Z.pos r) (evalE' (snd ab))
       -> preeval' (fst ab) < evalZ' m_enc
       -> preeval' (snd ab) < evalZ' m_enc
       -> eval' (Interp subZ' ab) = (eval' (fst ab) - eval' (snd ab))%F)
      /\ (small (Z.pos r) (evalE' (fst ab))
          -> small (Z.pos r) (evalE' (snd ab))
          -> preeval' (fst ab) < evalZ' m_enc
          -> preeval' (snd ab) < evalZ' m_enc
          -> 0 <= preeval' (Interp subZ' ab) < evalZ' m_enc)
      /\ (small (Z.pos r) (evalE' (fst ab))
          -> small (Z.pos r) (evalE' (snd ab))
          -> preeval' (fst ab) < evalZ' m_enc
          -> preeval' (snd ab) < evalZ' m_enc
          -> small (Z.pos r) (evalE' (Interp subZ' ab))).
  Proof.
    pose proof (proj2_sig (@sub_ext_gen r sz m m_enc r'' m_enc_correct_montgomery'' r_big'' m_enc_small'' map_m_enc'')) as H.
    cbv [sub_ext_gen proj1_sig] in H.
    eval_t.
  Qed.

  Definition eval_subZ ab := proj1 (subZ_gen ab).
  Definition bounded_eval_subZ ab := proj2 (subZ_gen ab).

  Lemma oppZ_gen
    : forall a,
      (small (Z.pos r) (evalE' a)
       -> preeval' a < evalZ' m_enc
       -> eval' (Interp oppZ' a) = F.opp (eval' a))
      /\ (small (Z.pos r) (evalE' a)
          -> preeval' a < evalZ' m_enc
          -> 0 <= preeval' (Interp oppZ' a) < evalZ' m_enc)
      /\ (small (Z.pos r) (evalE' a)
          -> preeval' a < evalZ' m_enc
          -> small (Z.pos r) (evalE' (Interp oppZ' a))).
  Proof.
    pose proof (proj2_sig (@opp_ext_gen r sz m m_enc r'' m_enc_correct_montgomery'' r_big'' m_enc_small'' map_m_enc'')) as H.
    cbv [opp_ext_gen proj1_sig] in H.
    eval_t.
  Qed.

  Definition eval_oppZ ab := proj1 (oppZ_gen ab).
  Definition bounded_eval_oppZ ab := proj2 (oppZ_gen ab).

  Lemma mulZ_gen
    : forall ab,
      (small (Z.pos r) (evalE' (fst ab))
       -> small (Z.pos r) (evalE' (snd ab))
       -> eval' (Interp mulZ' ab) = (eval' (fst ab) * eval' (snd ab))%F)
      /\ (small (Z.pos r) (evalE' (fst ab))
          -> small (Z.pos r) (evalE' (snd ab))
          -> preeval' (snd ab) < evalZ' m_enc
          -> 0 <= preeval' (Interp mulZ' ab) < evalZ' m_enc)
      /\ (small (Z.pos r) (evalE' (fst ab))
          -> small (Z.pos r) (evalE' (snd ab))
          -> preeval' (fst ab) < evalZ' m_enc
          -> preeval' (snd ab) < evalZ' m_enc
          -> small (Z.pos r) (evalE' (Interp mulZ' ab))).
  Proof.
    pose proof (proj2_sig (@mul_ext_gen r sz m m_enc r'' r'_correct' m'' m'_correct m_enc_correct_montgomery'' r_big'' m_big'' m_enc_small'')) as H.
    cbv [mul_ext_gen mul'_gen proj1_sig redc] in H.
    eval_t.
  Qed.

  Definition eval_mulZ ab := proj1 (mulZ_gen ab).
  Definition bounded_eval_mulZ ab := proj2 (mulZ_gen ab).

  Lemma eval_nonzeroZ_iff
    : forall a,
      small (Z.pos r) (evalE' a)
      -> preeval' a < evalZ' m_enc
      -> (Interp nonzeroZ' a = 0 <-> (eval' a = F.of_Z m 0)).
  Proof.
    pose proof (proj2_sig (@nonzero_ext_gen r sz m m_enc r'' m_enc_correct_montgomery'' r'_pow_correct'' r_big'' m_big'')) as H.
    cbv [nonzero_ext_gen nonzero proj1_sig] in H.
    eval_t.
  Qed.

  Lemma eval_nonzeroZ
    : forall a,
      small (Z.pos r) (evalE' a)
      -> preeval' a < evalZ' m_enc
      -> (Interp nonzeroZ' a =? 0)
         = (if Decidable.dec (eval' a = F.of_Z m 0) then true else false).
  Proof.
    intros a H0 H1.
    destruct (eval_nonzeroZ_iff a H0 H1).
    edestruct dec; destruct (Interp nonzeroZ' a =? 0) eqn:?; try reflexivity;
      Z.ltb_to_lt;
      exfalso; eauto.
  Qed.
End with_curves.
