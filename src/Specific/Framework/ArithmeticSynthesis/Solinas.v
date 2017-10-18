Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Import Coq.QArith.QArith_base.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.Saturated.Freeze.
Require Import Crypto.Arithmetic.Karatsuba.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Eta.
Require Import Crypto.Compilers.EtaInterp.
Require Import Crypto.Compilers.Linearize.
Require Import Crypto.Compilers.LinearizeInterp.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Reify.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.Tuple.
Require Import Crypto.Arithmetic.Compiled.Core.
Require Import Crypto.Arithmetic.Compiled.Karatsuba.
Require Import Crypto.Arithmetic.Compiled.Saturated.Freeze.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.HelperTactics.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.SideConditions.CorePackages.
Require Import Crypto.Util.SideConditions.AdmitPackage.
Require Import Crypto.Util.SideConditions.ReductionPackages.
Require Import Crypto.Util.SideConditions.RingPackage.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.PoseTermWithName.
Require Import Crypto.Util.Tactics.CacheTerm.
Require Import Crypto.Util.Curry.
Require Crypto.Util.Tuple.

Local Set Implicit Arguments.

Local Notation tuple := Tuple.tuple.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Infix "^" := tuple : type_scope.

Module Export Exports.
  Export Coq.setoid_ring.ZArithRing.
End Exports.

Local Ltac solve_constant_local_sig :=
  idtac;
  lazymatch goal with
  | [ |- { c : Z^?sz | Positional.Fdecode (m:=?M) ?wt c = ?v } ]
    => (exists (Positional.encode (n:=sz) (modulo_cps:=@modulo_cps) (div_cps:=@div_cps) wt (F.to_Z (m:=M) v)))
  end;
  abstract (
      setoid_rewrite Positional.Fdecode_Fencode_id;
      [ reflexivity
      | eauto using wt0_1, wt_nonzero, wt_divides', div_mod, sz_nonzero;
        intros; autorewrite with uncps push_id; auto using div_mod.. ]
    ).

Section gen.
  Import CurveParameters.CurveParameters.
  Context (curve : CurveParameters)
          (curve_sc : CurveParameterBaseSideConditions curve).

  Local Notation m := curve.(m).
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

  Definition constant_sig' v
    : { c : Z^sz | Positional.Fdecode (m:=m) wt c = v}.
  Proof. solve_constant_local_sig. Defined.

  Local Notation InterpC c
    := (flat_interp_tuple (interp_base_type:=interp_base_type) (n:=sz) (T:=Tbase TZ) (Interp c tt)).

  Definition constantE_sig' v
    : { c : Expr (Unit -> Tbase TZ^sz)
      | Positional.Fdecode (m:=m) wt (InterpC c)
        = v}.
  Proof.
    eexists (Compiler.compile_tupleZ (proj1_sig (constant_sig' v))).
    abstract (
        repeat first [ progress cbv [Interp Compiler.compile_tupleZ Compiler.compile_const interp]
                     | rewrite SmartMap.interpf_SmartPairf
                     | rewrite SmartMap.SmartVarfMap_compose
                     | rewrite SmartMap.SmartVarfMap_tuple
                     | progress cbn -[constant_sig']
                     | progress cbv [cast_const tuple_map SmartMap.SmartVarfMap]
                     | rewrite Tuple.map_id
                     | rewrite !flat_interp_tuple_untuple
                     | apply proj2_sig ]
      ).
  Defined.

  Definition zero_sig'
    : { zero : Z^sz | Positional.Fdecode (m:=m) wt zero = 0%F}
    := Eval hnf in constant_sig' _.

  Definition one_sig'
    : { one : Z^sz | Positional.Fdecode (m:=m) wt one = 1%F}
    := Eval hnf in constant_sig' _.

  Definition zeroE_sig'
    : { zero : Expr (Unit -> Tbase TZ^sz)
      | Positional.Fdecode (m:=m) wt (InterpC zero) = 0%F}
    := Eval hnf in constantE_sig' _.

  Definition oneE_sig'
    : { one : Expr (Unit -> Tbase TZ^sz)
      | Positional.Fdecode (m:=m) wt (InterpC one) = 1%F}
    := Eval hnf in constantE_sig' _.

  Local Notation admit := (match AdmitAxiom.proof_admitted with end).

  Record solinas_side_conditions :=
    {
      not_montgomery : vm_decide_package (curve.(montgomery) = false);

      vm_add_patterned : vm_compute_evar_package_vm_large (add_patterned wt sz);
      vm_sub_patterned : vm_compute_evar_package_vm_large (fun ab => sub_patterned wt sz (coef, ab));
      vm_mul_patterned : vm_compute_evar_package_vm_large (mul_patterned wt sz sz2);
      vm_opp_patterned : vm_compute_evar_package_vm_large (fun a => opp_patterned wt sz (coef, a));
      vm_reduce_patterned : vm_compute_evar_package_vm_large (reduce_patterned wt sz2 sz s c);
      vm_reduce_patterned_sz_sz : vm_compute_evar_package_vm_large (reduce_patterned wt sz sz s c);
      vm_reduce_patterned_sz_1p5 : vm_compute_evar_package_vm_large (reduce_patterned wt (sz + half_sz) sz s c);
      vm_chained_carries_reduce_patterned : vm_compute_evar_package_vm_large (chained_carries_reduce_patterned wt sz s c carry_chains);
      vm_karatsuba_mul_patterned
      : vm_compute_evar_package_vm_large (if curve.(karatsuba)
                                          then Some (karatsuba_mul_patterned wt half_sz sz sqrt_s)
                                          else None);
      vm_goldilocks_mul_patterned
      : vm_compute_evar_package_vm_large (if curve.(goldilocks)
                                          then Some (goldilocks_mul_patterned wt half_sz sz sqrt_s)
                                          else None);
      vm_freeze_patterned
      : vm_compute_evar_package_vm_large (if curve.(freeze)
                                          then Some (fun a => freeze_patterned wt sz (Z.ones bitwidth) (m_enc, a))
                                          else None);
      vm_compiled_preadd : vm_compute_evar_package_vm_large (compiled_preadd wt sz);
      vm_compiled_presub : vm_compute_evar_package_vm_large (Compiler.fill_first_of_pair_tupleZ (compiled_presub wt sz) coef);
      vm_compiled_premul : vm_compute_evar_package_vm_large (compiled_premul wt sz sz2);
      vm_compiled_preopp : vm_compute_evar_package_vm_large (Compiler.fill_first_of_pair_tupleZ (compiled_preopp wt sz) coef);
      vm_compiled_prereduce : vm_compute_evar_package_vm_large (compiled_prereduce wt sz2 sz s c);
      vm_compiled_prereduce_sz_sz : vm_compute_evar_package_vm_large (compiled_prereduce wt sz sz s c);
      vm_compiled_prereduce_sz_1p5 : vm_compute_evar_package_vm_large (compiled_prereduce wt (sz + half_sz) sz s c);
      vm_compiled_prechained_carries_reduce : vm_compute_evar_package_vm_large (compiled_prechained_carries_reduce wt sz s c carry_chains);
      vm_compiled_prekaratsuba_mul
      : vm_compute_evar_package_vm_large (if curve.(karatsuba)
                                          then Some (compiled_prekaratsuba_mul wt half_sz sz sqrt_s)
                                          else None);
      vm_compiled_pregoldilocks_mul
      : vm_compute_evar_package_vm_large (if curve.(goldilocks)
                                          then Some (compiled_pregoldilocks_mul wt half_sz sz sqrt_s)
                                          else None);
      vm_compiled_prefreeze
      : vm_compute_evar_package_vm_large (if curve.(freeze)
                                          then Some (Compiler.fill_first_of_pair_tupleZ
                                                       (compiled_prefreeze wt sz (Z.ones bitwidth))
                                                       m_enc)
                                          else None);
      mul_code_correct
      : match mul_code with
        | None => True
        | Some v
          => eq_by_Zring_prod_package
               (forall a b,
                   v a b
                   = let ab := Compiler.do_apply (val vm_mul_patterned (a, b)) in
                     Compiler.do_apply (val vm_reduce_patterned ab))
        end;
      square_code_correct
      : match square_code with
        | None => True
        | Some v
          => eq_by_Zring_prod_package
               (forall a,
                   v a
                   = let aa := Compiler.do_apply (val vm_mul_patterned (a, a)) in
                     Compiler.do_apply (val vm_reduce_patterned aa))
        end;

      evalZ := Positional.Fdecode (sz:=sz) (m:=m) wt;
      evalZ2 := Positional.Fdecode (sz:=sz2) (m:=m) wt;
      evalZ1p5 := Positional.Fdecode (sz:=sz+half_sz) (m:=m) wt;
      evalE := flat_interp_tuple (interp_base_type:=interp_base_type) (n:=sz) (T:=Tbase TZ);
      evalE2 := flat_interp_tuple (interp_base_type:=interp_base_type) (n:=sz2) (T:=Tbase TZ);
      evalE1p5 := flat_interp_tuple (interp_base_type:=interp_base_type) (n:=sz+half_sz) (T:=Tbase TZ);
      eval x := evalZ (evalE x);
      eval2 x := evalZ2 (evalE2 x);
      eval1p5 x := evalZ1p5 (evalE1p5 x);

      mul_code_casted : option (interp_type interp_base_type (exprT sz 2 sz))
      := option_map (fun mul xy => flat_interp_untuple (T:=Tbase TZ) (mul (evalE (fst xy)) (evalE (snd xy))))
                    mul_code;
      square_code_casted : option (interp_type interp_base_type (exprT sz 1 sz))
      := option_map (fun square x => flat_interp_untuple (T:=Tbase TZ) (square (evalE x)))
                    square_code;

      mul_codeZ : optional_evar_rel_package
                    (@Reify_evar_package (exprT sz 2 sz))
                    mul_code_casted;
      square_codeZ : optional_evar_rel_package
                       (@Reify_evar_package (exprT sz 1 sz))
                       square_code_casted;

      zeroZ : vm_compute_evar_package_vm_small (proj1_sig zeroE_sig');
      oneZ : vm_compute_evar_package_vm_small (proj1_sig oneE_sig');

      addZ : unoption_Expr_evar_package 2 (val vm_compiled_preadd);
      subZ : unoption_Expr_evar_package 2 (val vm_compiled_presub);
      oppZ : unoption_Expr_evar_package 1 (val vm_compiled_preopp);
      carryZ : unoption_Expr_evar_package 1 (val vm_compiled_prechained_carries_reduce);
      reduceZ : unoption_Expr_evar_package 1 (val vm_compiled_prereduce);
      reduceZ_sz_sz : unoption_Expr_evar_package 1 (val vm_compiled_prereduce_sz_sz);
      reduceZ_sz_1p5 : unoption_Expr_evar_package 1 (val vm_compiled_prereduce_sz_1p5);
      premulZ : unoption_Expr_evar_package 2 (val vm_compiled_premul);
      val_presquareZ : Expr (exprT sz 1 sz2)
      := fun var => Abs (fun x => invert_Abs (val premulZ var) (x, x));
      prekaratsuba_mulZ : optional_evar_rel_package (unoption_Expr_evar_package (sz:=sz) (szR:=sz) 2) (val vm_compiled_prekaratsuba_mul);
      pregoldilocks_mulZ : optional_evar_rel_package (unoption_Expr_evar_package (sz:=sz) (szR:=sz+half_sz) 2) (val vm_compiled_pregoldilocks_mul);
      val_prekaratsuba_squareZ : option (Expr (exprT sz 1 sz))
      := option_map (fun prekaratsuba_mulZ : Expr (exprT sz 2 sz)
                     => fun var => Abs (fun x => invert_Abs (prekaratsuba_mulZ var) (x, x)))
                    (val prekaratsuba_mulZ);
      val_pregoldilocks_squareZ : option (Expr (exprT sz 1 (sz+half_sz)))
      := option_map (fun pregoldilocks_mulZ : Expr (exprT sz 2 (sz+half_sz))
                     => fun var => Abs (fun x => invert_Abs (pregoldilocks_mulZ var) (x, x)))
                    (val pregoldilocks_mulZ);
      freezeZ : optional_evar_rel_package (unoption_Expr_evar_package (sz:=sz) (szR:=sz) 1) (val vm_compiled_prefreeze);
      carry_mulZ
      := ExprEta
           (Linearize
              ((val carryZ)
                 ∘ match val mul_codeZ, val pregoldilocks_mulZ, val prekaratsuba_mulZ with
                   | Some mul, _, _ => val reduceZ_sz_sz ∘ mul
                   | None, Some gmul, _ => val reduceZ_sz_1p5 ∘ gmul
                   | None, None, Some kmul => val reduceZ_sz_sz ∘ kmul
                   | None, None, None => val reduceZ ∘ val premulZ
                   end)%expr);
      carry_squareZ
      := ExprEta
           (Linearize
              ((val carryZ)
                 ∘ match val square_codeZ, val_pregoldilocks_squareZ, val_prekaratsuba_squareZ with
                   | Some square, _, _ => val reduceZ_sz_sz ∘ square
                   | None, Some gsquare, _ => val reduceZ_sz_1p5 ∘ gsquare
                   | None, None, Some ksquare => val reduceZ_sz_sz ∘ ksquare
                   | None, None, None => val reduceZ ∘ val_presquareZ
                   end)%expr);
      carry_addZ := (val carryZ ∘ val addZ)%expr;
      carry_subZ := (val carryZ ∘ val subZ)%expr;
      carry_oppZ := (val carryZ ∘ val oppZ)%expr;

      interp_addZ
      : eq_by_Zring_prod_package
          (forall x y, evalE (Interp (val addZ) (x, y))
                       = Compiler.do_apply (val vm_add_patterned (evalE x, evalE y)));
      interp_subZ
      : eq_by_Zring_prod_package
          (forall x y, evalE (Interp (val subZ) (x, y))
                       = Compiler.do_apply (val vm_sub_patterned (evalE x, evalE y)));
      interp_oppZ
      : eq_by_Zring_prod_package
          (forall x, evalE (Interp (val oppZ) x)
                     = Compiler.do_apply (val vm_opp_patterned (evalE x)));
      interp_carryZ
      : admit_package
          (eq_by_Zring_prod_package
             (forall x, evalE (Interp (val carryZ) x)
                        = Compiler.do_apply (val vm_chained_carries_reduce_patterned (evalE x))))
      := admit;
      interp_reduceZ
      : admit_package
          (eq_by_Zring_prod_package
             (forall x, evalE (Interp (val reduceZ) x)
                        = Compiler.do_apply (val vm_reduce_patterned (evalE2 x))))
      := admit;
      interp_reduceZ_sz_sz
      : admit_package
          (eq_by_Zring_prod_package
             (forall x, evalE (Interp (val reduceZ_sz_sz) x)
                        = Compiler.do_apply (val vm_reduce_patterned_sz_sz (evalE x))))
      := admit;
      interp_reduceZ_sz_1p5
      : admit_package
          (eq_by_Zring_prod_package
             (forall x, evalE (Interp (val reduceZ_sz_1p5) x)
                        = Compiler.do_apply (val vm_reduce_patterned_sz_1p5 (evalE1p5 x))))
      := admit;
      interp_premulZ
      : admit_package
          (forall x y, evalE2 (Interp (val premulZ) (x, y))
                    = Compiler.do_apply (val vm_mul_patterned (evalE x, evalE y)))
      := admit;
      interp_prekaratsuba_mulZ
      : admit_package
          (forall x y, option_map
                         (fun prekaratsuba_mulZ : Expr (exprT sz 2 sz)
                          => evalE (Interp prekaratsuba_mulZ (x, y)))
                         (val prekaratsuba_mulZ)
                       = option_map
                           (fun vm_karatsuba_mul_patterned
                            => Compiler.do_apply (vm_karatsuba_mul_patterned (evalE x, evalE y)))
                           (val vm_karatsuba_mul_patterned))
      := admit;
      interp_pregoldilocks_mulZ
      : admit_package
          (forall x y, option_map
                         (fun pregoldilocks_mulZ : Expr (exprT sz 2 (sz+half_sz))
                          => evalE1p5 (Interp pregoldilocks_mulZ (x, y)))
                         (val pregoldilocks_mulZ)
                       = option_map
                           (fun vm_goldilocks_mul_patterned
                            => Compiler.do_apply (vm_goldilocks_mul_patterned (evalE x, evalE y)))
                           (val vm_goldilocks_mul_patterned))
      := admit;
      interp_freezeZ
      : admit_package
          (forall x, option_map
                       (fun freezeZ : Expr (exprT sz 1 sz)
                        => evalE (Interp freezeZ x))
                       (val freezeZ)
                     = option_map
                         (fun vm_freeze_patterned
                          => Compiler.do_apply (vm_freeze_patterned (evalE x)))
                         (val vm_freeze_patterned))
      := admit;

    }.

  Context (curve_scd : solinas_side_conditions).

  Local Notation evalZ' := curve_scd.(evalZ).
  Local Notation evalZ2' := curve_scd.(evalZ2).
  Local Notation evalZ1p5' := curve_scd.(evalZ1p5).
  Local Notation evalE' := curve_scd.(evalE).
  Local Notation eval' := curve_scd.(eval).
  Local Notation eval2' := curve_scd.(eval2).
  Local Notation eval1p5' := curve_scd.(eval1p5).
  Local Notation zeroZ' := (val curve_scd.(zeroZ)).
  Local Notation oneZ' := (val curve_scd.(oneZ)).
  Local Notation addZ' := (val curve_scd.(addZ)).
  Local Notation subZ' := (val curve_scd.(subZ)).
  Local Notation oppZ' := (val curve_scd.(oppZ)).
  Local Notation carryZ' := (val curve_scd.(carryZ)).
  Local Notation reduceZ' := (val curve_scd.(reduceZ)).
  Local Notation reduceZ_sz_sz' := (val curve_scd.(reduceZ_sz_sz)).
  Local Notation reduceZ_sz_1p5' := (val curve_scd.(reduceZ_sz_1p5)).
  Local Notation premulZ' := (val curve_scd.(premulZ)).
  Local Notation freezeZ' := (val curve_scd.(freezeZ)).
  Local Notation prekaratsuba_mulZ' := (val curve_scd.(prekaratsuba_mulZ)).
  Local Notation pregoldilocks_mulZ' := (val curve_scd.(pregoldilocks_mulZ)).
  Local Notation presquareZ' := curve_scd.(val_presquareZ).
  Local Notation prekaratsuba_squareZ' := curve_scd.(val_prekaratsuba_squareZ).
  Local Notation pregoldilocks_squareZ' := curve_scd.(val_pregoldilocks_squareZ).
  Local Notation carry_mulZ' := curve_scd.(carry_mulZ).
  Local Notation carry_squareZ' := curve_scd.(carry_squareZ).
  Local Notation carry_addZ' := curve_scd.(carry_addZ).
  Local Notation carry_subZ' := curve_scd.(carry_subZ).
  Local Notation carry_oppZ' := curve_scd.(carry_oppZ).

  Lemma eval_zeroZ
    : eval' (Interp zeroZ' tt) = 0%F.
  Proof. rewrite evar_package_pf_eq; apply proj2_sig. Qed.
  Lemma eval_oneZ
    : eval' (Interp oneZ' tt) = 1%F.
  Proof. rewrite evar_package_pf_eq; apply proj2_sig. Qed.

  Local Ltac eval_t_whenever :=
    repeat first [ progress cbn in *
                 | progress intros
                 | progress cbv [eval' evalZ' eval2' evalZ2' eval1p5' evalZ1p5' mul_code_casted square_code_casted LetIn.Let_In] in *
                 | progress subst
                 | progress destruct_head'_prod
                 | progress destruct_head'_sig
                 | exfalso; assumption
                 | rewrite add_patterned_correct
                 | rewrite sub_patterned_correct
                 | rewrite mul_patterned_correct
                 | rewrite opp_patterned_correct
                 | rewrite reduce_patterned_correct
                 | rewrite chained_carries_reduce_patterned_correct
                 | rewrite karatsuba_mul_patterned_correct
                 | rewrite goldilocks_mul_patterned_correct
                 | rewrite freeze_patterned_correct
                 | rewrite (evar_package_pf_eq curve_scd.(vm_add_patterned))
                 | rewrite (evar_package_pf_eq curve_scd.(vm_sub_patterned))
                 | rewrite (evar_package_pf_eq curve_scd.(vm_opp_patterned))
                 | rewrite (evar_package_pf_eq curve_scd.(vm_mul_patterned))
                 | rewrite (evar_package_pf_eq curve_scd.(vm_reduce_patterned))
                 | rewrite (evar_package_pf_eq curve_scd.(vm_reduce_patterned_sz_sz))
                 | rewrite (evar_package_pf_eq curve_scd.(vm_reduce_patterned_sz_1p5))
                 | rewrite (evar_package_pf_eq curve_scd.(vm_chained_carries_reduce_patterned))
                 | rewrite (evar_package_pf_eq curve_scd.(vm_karatsuba_mul_patterned))
                 | rewrite (evar_package_pf_eq curve_scd.(vm_goldilocks_mul_patterned))
                 | rewrite (evar_package_pf_eq curve_scd.(vm_freeze_patterned))
                 | rewrite interp_addZ
                 | rewrite interp_subZ
                 | rewrite interp_oppZ
                 | rewrite interp_carryZ
                 | rewrite interp_reduceZ
                 | rewrite interp_reduceZ_sz_sz
                 | rewrite interp_reduceZ_sz_1p5
                 | rewrite interp_premulZ
                 | rewrite interp_prekaratsuba_mulZ
                 | rewrite interp_pregoldilocks_mulZ
                 | rewrite interp_freezeZ
                 | setoid_rewrite flat_interp_tuple_untuple
                 | match goal with
                   | [ H : true = false |- _ ] => exfalso; clear -H; discriminate
                   | [ H : false = true |- _ ] => exfalso; clear -H; discriminate
                   | [ |- option_map (fun e => ?f (@?g e)) ?o = _ ]
                     => lazymatch f with
                        | Positional.Fdecode _
                          => transitivity (option_map f (option_map g o));
                             [ destruct o; reflexivity | ]
                        end
                   | [ |- Some _ = Some _ ] => apply f_equal
                   | [ |- ?x = ?x ] => reflexivity
                   | [ |- context[option_map _ (CorePackages.val ?pkg)] ]
                     => pose proof (CorePackages.evar_package_pf pkg); destruct pkg; cbn in *
                   | [ H : context[match CorePackages.val ?pkg with None => _ | _ => _ end] |- _ ]
                     => pose proof (CorePackages.evar_package_pf pkg); destruct pkg; cbn in *
                   end
                 | break_innermost_match_hyps_step
                 | progress cbv [Interp] in *
                 | match goal with
                   | [ H : _ |- _ ] => rewrite H; clear H
                   end ].
  Local Ltac eval_t_fin :=
    F_mod_eq;
    repeat autounfold; repeat autorewrite with uncps push_id push_basesystem_eval;
    try reflexivity; try eassumption.

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
    pose proof div_correct; pose proof modulo_correct.
  Local Ltac eval_t_pose_freeze :=
    pose proof m_correct_wt;
    pose proof m_enc_correct.
  Local Ltac eval_t_pose_goldilocks :=
    pose proof sqrt_s_nonzero;
    pose proof sqrt_s_correct;
    pose proof fst_nat_divmod_sz_nonzero.

  Local Ltac eval_t :=
    eval_t_pose;
    eval_t_whenever;
    try eval_t_fin.

  Lemma eval_addZ
    : forall ab,
      eval' (Interp addZ' ab) = (eval' (fst ab) + eval' (snd ab))%F.
  Proof. eval_t. Qed.

  Lemma eval_subZ
    : forall ab,
      eval' (Interp subZ' ab) = (eval' (fst ab) - eval' (snd ab))%F.
  Proof. eval_t. Qed.

  Lemma eval_oppZ
    : forall a,
      eval' (Interp oppZ' a) = F.opp (eval' a).
  Proof. eval_t. Qed.

  Lemma eval_carryZ
    : forall a,
      eval' (Interp carryZ' a) = eval' a.
  Proof. eval_t. Qed.

  Lemma eval_reduceZ
    : forall a,
      eval' (Interp reduceZ' a) = eval2' a.
  Proof. eval_t. Qed.

  Lemma eval_reduceZ_sz_sz
    : forall a,
      eval' (Interp reduceZ_sz_sz' a) = eval' a.
  Proof. eval_t. Qed.

  Lemma eval_reduceZ_sz_1p5
    : forall a,
      eval' (Interp reduceZ_sz_1p5' a) = eval1p5' a.
  Proof. eval_t. Qed.

  Lemma eval_premulZ
    : forall ab,
      eval2' (Interp premulZ' ab) = (eval' (fst ab) * eval' (snd ab))%F.
  Proof. eval_t. Qed.

  Lemma eval_presquareZ
    : forall a,
      eval2' (Interp presquareZ' a) = (eval' a * eval' a)%F.
  Proof.
    cbn; intro a; setoid_rewrite <- (eval_premulZ (a, a)); cbn.
    cbv [Interp]; rewrite <- interpf_invert_Abs.
    reflexivity.
  Qed.

  Lemma eval_prekaratsuba_mulZ
    : forall ab,
      option_map (fun prekaratsuba_mulZ : Expr (exprT sz 2 sz)
                  => eval' (Interp prekaratsuba_mulZ ab))
                 prekaratsuba_mulZ'
      = option_map (fun _ => (eval' (fst ab) * eval' (snd ab))%F)
                   prekaratsuba_mulZ'.
  Proof. eval_t_pose_goldilocks; eval_t. Qed.

  Lemma eval_prekaratsuba_squareZ
    : forall a,
      option_map (fun prekaratsuba_squareZ : Expr (exprT sz 1 sz)
                  => eval' (Interp prekaratsuba_squareZ a))
                 prekaratsuba_squareZ'
      = option_map (fun _ => (eval' a * eval' a)%F) prekaratsuba_squareZ'.
  Proof.
    cbn; intro a.
    cbv [prekaratsuba_squareZ'].
    rewrite !option_map_map.
    setoid_rewrite <- (eval_prekaratsuba_mulZ (a, a)); cbn.
    destruct prekaratsuba_mulZ'; [ | reflexivity ]; cbn.
    cbv [Interp]; rewrite <- interpf_invert_Abs.
    reflexivity.
  Qed.

  Lemma eval_pregoldilocks_mulZ
    : forall ab,
      option_map (fun pregoldilocks_mulZ : Expr (exprT sz 2 (sz+half_sz))
                  => eval1p5' (Interp pregoldilocks_mulZ ab))
                 pregoldilocks_mulZ'
      = option_map (fun _ => (eval' (fst ab) * eval' (snd ab))%F)
                   pregoldilocks_mulZ'.
  Proof. eval_t_pose_goldilocks; eval_t. Qed.

  Lemma eval_pregoldilocks_squareZ
    : forall a,
      option_map (fun pregoldilocks_squareZ : Expr (exprT sz 1 (sz+half_sz))
                  => eval1p5' (Interp pregoldilocks_squareZ a))
                 pregoldilocks_squareZ'
      = option_map (fun _ => (eval' a * eval' a)%F) pregoldilocks_squareZ'.
  Proof.
    cbn; intro a.
    cbv [pregoldilocks_squareZ'].
    rewrite !option_map_map.
    setoid_rewrite <- (eval_pregoldilocks_mulZ (a, a)); cbn.
    destruct pregoldilocks_mulZ'; [ | reflexivity ]; cbn.
    cbv [Interp]; rewrite <- interpf_invert_Abs.
    reflexivity.
  Qed.

  Lemma eval_freezeZ
    : forall a,
      (0 <= Positional.eval wt (evalE' a) < 2 * Z.pos m)
      -> option_map (fun freezeZ : Expr (exprT sz 1 sz)
                     => eval' (Interp freezeZ a))
                    freezeZ'
         = option_map (fun _ => eval' a)
                      freezeZ'.
  Proof. eval_t_pose_freeze; eval_t. Qed.

  Lemma eval_carry_mulZ
    : forall ab,
      eval' (Interp carry_mulZ' ab) = (eval' (fst ab) * eval' (snd ab))%F.
  Proof.
    cbn -[Linearize ExprEta]; cbv [carry_mulZ'].
    intro ab.
    rewrite InterpExprEta_arrow, InterpLinearize, InterpCompose, eval_carryZ.
    destruct (curve_scd.(mul_codeZ)) as [ [?|] ?].
    { pose proof (curve_scd.(mul_code_correct)).
      cbn [val]; intros; rewrite InterpCompose, eval_reduceZ_sz_sz.
      eval_t. }
    { cbn -[Interp Compose] in *.
      pose proof (eval_pregoldilocks_mulZ ab) as Hg.
      pose proof (eval_prekaratsuba_mulZ ab) as Hk.
      destruct curve_scd.(pregoldilocks_mulZ) as [ [?|] ?];
        [ | destruct curve_scd.(prekaratsuba_mulZ) as [ [?|] ?] ];
        cbn [val]; cbn in * |- ; inversion_option;
          rewrite InterpCompose;
          first [ rewrite eval_reduceZ_sz_sz
                | rewrite eval_reduceZ
                | rewrite eval_reduceZ_sz_1p5 ].
      { rewrite Hg; reflexivity. }
      { rewrite Hk; reflexivity. }
      { rewrite eval_premulZ; reflexivity. } }
  Qed.

  Lemma eval_carry_squareZ
    : forall a,
      eval' (Interp carry_squareZ' a) = (eval' a * eval' a)%F.
  Proof.
    cbn -[Linearize ExprEta]; cbv [carry_squareZ'].
    intro ab.
    rewrite InterpExprEta_arrow, InterpLinearize, InterpCompose, eval_carryZ.
    destruct (curve_scd.(square_codeZ)) as [ [?|] ?].
    { pose proof (curve_scd.(square_code_correct)).
      cbn [val]; intros; rewrite InterpCompose, eval_reduceZ_sz_sz.
      eval_t. }
    { cbn -[Interp Compose] in *.
      pose proof (eval_pregoldilocks_squareZ ab) as Hg.
      pose proof (eval_prekaratsuba_squareZ ab) as Hk.
      cbv [pregoldilocks_squareZ' prekaratsuba_squareZ'] in *.
      destruct curve_scd.(pregoldilocks_mulZ) as [ [?|] ?];
        [ | destruct curve_scd.(prekaratsuba_mulZ) as [ [?|] ?] ];
        cbn [val option_map]; cbn in * |- ; inversion_option;
          rewrite InterpCompose;
          first [ rewrite eval_reduceZ_sz_sz
                | rewrite eval_reduceZ
                | rewrite eval_reduceZ_sz_1p5 ].
      { cbn; rewrite Hg; reflexivity. }
      { cbn; rewrite Hk; reflexivity. }
      { rewrite eval_presquareZ; reflexivity. } }
  Qed.

  Lemma eval_carry_addZ
    : forall ab,
      eval' (Interp carry_addZ' ab) = (eval' (fst ab) + eval' (snd ab))%F.
  Proof.
    cbn; cbv [carry_addZ' LetIn.Let_In].
    setoid_rewrite eval_carryZ; setoid_rewrite eval_addZ; reflexivity.
  Qed.

  Lemma eval_carry_subZ
    : forall ab,
      eval' (Interp carry_subZ' ab) = (eval' (fst ab) - eval' (snd ab))%F.
  Proof.
    cbn; cbv [carry_subZ' LetIn.Let_In].
    setoid_rewrite eval_carryZ; setoid_rewrite eval_subZ; reflexivity.
  Qed.

  Lemma eval_carry_oppZ
    : forall a,
      eval' (Interp carry_oppZ' a) = F.opp (eval' a).
  Proof.
    cbn; cbv [carry_oppZ' LetIn.Let_In].
    setoid_rewrite eval_carryZ; setoid_rewrite eval_oppZ; reflexivity.
  Qed.

  Local Definition ring_pkg : { T : _ & T }.
  Proof.
    eexists.
    refine (Ring.ring_by_isomorphism
              (F := F m)
              (H := interp_flat_type interp_base_type (Tbase TZ^sz))
              (phi := fun x => flat_interp_untuple (T:=Tbase TZ) (Positional.Fencode (div_cps:=@div_cps) (modulo_cps:=@modulo_cps) wt x))
              (phi' := eval')
              (zero := Interp zeroZ' tt)
              (one := Interp oneZ' tt)
              (add := fun x y => Interp carry_addZ' (x, y))
              (sub := fun x y => Interp carry_subZ' (x, y))
              (opp := Interp carry_oppZ')
              (mul := fun x y => Interp carry_mulZ' (x, y))
              (phi'_opp := eval_carry_oppZ)
              _
              _
              _
              _
              _).
    { abstract (
          cbv [eval' evalZ']; setoid_rewrite flat_interp_tuple_untuple;
          refine (Positional.Fdecode_Fencode_id
                    (sz_nonzero := sz_nonzero)
                    (div_mod := div_mod)
                    wt wt0_1 wt_nonzero wt_divides');
          eauto using @modulo_id, @div_id
        ). }
    { cbv [eval' evalZ']; intros; apply Positional.eq_Feq_iff. }
    { apply eval_zeroZ. }
    { apply eval_oneZ. }
    { intros; apply eval_carry_addZ. }
    { intros; apply eval_carry_subZ. }
    { intros; apply eval_carry_mulZ. }
  Defined.

  Definition ring : _ /\ _ /\ _
    := Eval cbv [ring_pkg projT2] in
        projT2 ring_pkg.
End gen.
(*
Ltac internal_solve_code_correct P_tac :=
  hnf;
  lazymatch goal with
  | [ |- True ] => constructor
  | _
    => cbv [Positional.mul_cps Positional.reduce_cps];
       intros;
       autorewrite with pattern_runtime;
       repeat autounfold;
       autorewrite with pattern_runtime;
       basesystem_partial_evaluation_RHS;
       P_tac ();
       break_match; cbv [Let_In runtime_mul runtime_add]; repeat apply (f_equal2 pair); rewrite ?Z.shiftl_mul_pow2 by omega; ring
  end.

Ltac pose_mul_code_correct P_extra_prove_mul_eq sz sz2 wt s c mul_code mul_code_correct :=
  cache_proof_with_type_by
    (match mul_code with
     | None => True
     | Some v
       => forall a b,
         v a b
         = Positional.mul_cps (n:=sz) (m:=sz2) wt a b
                              (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)
     end)
    ltac:(internal_solve_code_correct P_extra_prove_mul_eq)
           mul_code_correct.

Ltac pose_square_code_correct P_extra_prove_square_eq sz sz2 wt s c square_code square_code_correct :=
  cache_proof_with_type_by
    (match square_code with
     | None => True
     | Some v
       => forall a,
         v a
         = Positional.mul_cps (n:=sz) (m:=sz2) wt a a
                              (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)
     end)
    ltac:(internal_solve_code_correct P_extra_prove_square_eq)
           square_code_correct.

Ltac cache_sig_with_type_by_existing_sig ty existing_sig id :=
  cache_sig_with_type_by_existing_sig_helper
    ltac:(fun _ => cbv [carry_sig' constant_sig' zero_sig' one_sig' add_sig' sub_sig' mul_sig' square_sig' opp_sig'])
           ty existing_sig id.

Ltac pose_carry_sig wt m base sz s c carry_chains carry_sig :=
  cache_sig_with_type_by_existing_sig
    {carry : (Z^sz -> Z^sz)%type |
     forall a : Z^sz,
       let eval := Positional.Fdecode (m := m) wt in
       eval (carry a) = eval a}
    (carry_sig' m base sz s c carry_chains)
    carry_sig.

Ltac pose_zero_sig wt m base sz sz_nonzero base_pos zero_sig :=
  cache_vm_sig_with_type
    { zero : Z^sz | Positional.Fdecode (m:=m) wt zero = 0%F}
    (zero_sig' m base sz sz_nonzero base_pos)
    zero_sig.

Ltac pose_one_sig wt m base sz sz_nonzero base_pos one_sig :=
  cache_vm_sig_with_type
    { one : Z^sz | Positional.Fdecode (m:=m) wt one = 1%F}
    (one_sig' m base sz sz_nonzero base_pos)
    one_sig.

Ltac pose_add_sig wt m base sz add_sig :=
  cache_sig_with_type_by_existing_sig
    { add : (Z^sz -> Z^sz -> Z^sz)%type |
      forall a b : Z^sz,
        let eval := Positional.Fdecode (m:=m) wt in
        eval (add a b) = (eval a + eval b)%F }
    (add_sig' m base sz)
    add_sig.

Ltac pose_sub_sig wt m base sz coef sub_sig :=
  cache_sig_with_type_by_existing_sig
    {sub : (Z^sz -> Z^sz -> Z^sz)%type |
     forall a b : Z^sz,
       let eval := Positional.Fdecode (m:=m) wt in
       eval (sub a b) = (eval a - eval b)%F}
    (sub_sig' m base sz coef)
    sub_sig.

Ltac pose_opp_sig wt m base sz coef opp_sig :=
  cache_sig_with_type_by_existing_sig
    {opp : (Z^sz -> Z^sz)%type |
     forall a : Z^sz,
       let eval := Positional.Fdecode (m := m) wt in
       eval (opp a) = F.opp (eval a)}
    (opp_sig' m base sz coef)
    opp_sig.

Ltac pose_mul_sig wt m base sz s c mul_code sz_nonzero s_nonzero base_pos mul_code_correct mul_sig :=
  cache_sig_with_type_by_existing_sig
    {mul : (Z^sz -> Z^sz -> Z^sz)%type |
     forall a b : Z^sz,
       let eval := Positional.Fdecode (m := m) wt in
       eval (mul a b) = (eval a * eval b)%F}
    (mul_sig' m base sz s c mul_code sz_nonzero s_nonzero base_pos mul_code_correct)
    mul_sig.

Ltac pose_square_sig wt m base sz s c square_code sz_nonzero s_nonzero base_pos square_code_correct square_sig :=
  cache_sig_with_type_by_existing_sig
    {square : (Z^sz -> Z^sz)%type |
     forall a : Z^sz,
       let eval := Positional.Fdecode (m := m) wt in
       eval (square a) = (eval a * eval a)%F}
    (square_sig' m base sz s c square_code sz_nonzero s_nonzero base_pos square_code_correct)
    square_sig.

Ltac pose_ring sz m wt wt_divides' sz_nonzero wt_nonzero zero_sig one_sig opp_sig add_sig sub_sig mul_sig ring :=
  cache_term
    (Ring.ring_by_isomorphism
       (F := F m)
       (H := Z^sz)
       (phi := Positional.Fencode wt)
       (phi' := Positional.Fdecode wt)
       (zero := proj1_sig zero_sig)
       (one := proj1_sig one_sig)
       (opp := proj1_sig opp_sig)
       (add := proj1_sig add_sig)
       (sub := proj1_sig sub_sig)
       (mul := proj1_sig mul_sig)
       (phi'_zero := proj2_sig zero_sig)
       (phi'_one := proj2_sig one_sig)
       (phi'_opp := proj2_sig opp_sig)
       (Positional.Fdecode_Fencode_id
          (sz_nonzero := sz_nonzero)
          (div_mod := div_mod)
          (modulo_cps_id:=@Core.modulo_id)
          (div_cps_id:=@Core.div_id)
          wt eq_refl wt_nonzero wt_divides')
       (Positional.eq_Feq_iff wt)
       (proj2_sig add_sig)
       (proj2_sig sub_sig)
       (proj2_sig mul_sig)
    )
    ring.

(*
Eval cbv [proj1_sig add_sig] in (proj1_sig add_sig).
Eval cbv [proj1_sig sub_sig] in (proj1_sig sub_sig).
Eval cbv [proj1_sig opp_sig] in (proj1_sig opp_sig).
Eval cbv [proj1_sig mul_sig] in (proj1_sig mul_sig).
Eval cbv [proj1_sig carry_sig] in (proj1_sig carry_sig).
 *)
*)
