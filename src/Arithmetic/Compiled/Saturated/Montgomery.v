Require Import Coq.ZArith.BinInt.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Definition.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Proofs.
Require Import Crypto.Arithmetic.Core. Import B.
Require Crypto.Arithmetic.Saturated.MontgomeryAPIUnfolder.
Require Crypto.Arithmetic.Saturated.MontgomeryAPI.
Require Import Crypto.Arithmetic.Compiled.Compiler.

Hint Unfold
     redc_cps
     pre_redc_cps
     redc_loop_cps
     redc_body_cps
     add sub opp nonzero
     add_cps sub_cps opp_cps nonzero_cps
     MontgomeryAPI.T
     MontgomeryAPI.zero
     MontgomeryAPI.nonzero_cps
     MontgomeryAPI.join0_cps
     MontgomeryAPI.divmod_cps
     MontgomeryAPI.drop_high_cps
     MontgomeryAPI.scmul_cps
     MontgomeryAPI.add_cps
     MontgomeryAPI.add_S1_cps
     MontgomeryAPI.add_S2_cps
     MontgomeryAPI.sub_then_maybe_add_cps
     MontgomeryAPI.conditional_sub_cps
     UniformWeight.uweight
  : basesystem_partial_evaluation_unfolder.

Hint Unfold
     redc_cps
     pre_redc_cps
     redc_loop_cps
     redc_body_cps
     add sub opp nonzero
     add_cps sub_cps opp_cps nonzero_cps
 : arithmetic_cps_unfolder parameterized_sig_unfolder.


Ltac basesystem_partial_evaluation_unfolder t :=
  let t := (eval cbv delta [
                   redc_cps
                     pre_redc_cps
                     redc_loop_cps
                     redc_body_cps
                     add sub opp nonzero
                     add_cps sub_cps opp_cps nonzero_cps
                 ] in t) in
  let t := Arithmetic.Saturated.MontgomeryAPI.basesystem_partial_evaluation_unfolder t in
  t.

Ltac Arithmetic.Core.basesystem_partial_evaluation_default_unfolder t ::=
  basesystem_partial_evaluation_unfolder t.

Definition redc_patterned (r : positive) (R_numlimbs : nat)
           (A_numlimbs : nat) (k : Z)
           (NAB : Tuple.tuple Z R_numlimbs * (Tuple.tuple Z A_numlimbs * Tuple.tuple Z R_numlimbs))
  := do_pattern_strip (@redc_cps r R_numlimbs (fst NAB) A_numlimbs (fst (snd NAB)) (snd (snd NAB)) k _ id).

Definition redc_patterned_correct r R_numlimbs A_numlimbs k NAB
  : do_apply (redc_patterned r R_numlimbs A_numlimbs k NAB)
    = @redc_cps r R_numlimbs (fst NAB) A_numlimbs (fst (snd NAB)) (snd (snd NAB)) k _ id
  := eq_refl.

Definition compiled_preredc_sig (r : positive) (R_numlimbs : nat)
           (A_numlimbs : nat) (k : Z)
  : { t : _ & t }.
Proof.
  do_compile_sig
    (fun n m T (f : Tuple.tuple _ _ -> _) NAB k => @redc_cps r n (fst NAB) m (fst (snd NAB)) (snd (snd NAB)) k T f)
    uconstr:(fun t xy => t R_numlimbs A_numlimbs xy k).
Defined.

Definition compiled_preredc' r R_numlimbs A_numlimbs k
  := Eval cbv [projT2 projT1 compiled_preredc_sig] in
      projT2 (compiled_preredc_sig r R_numlimbs A_numlimbs k).

Definition add_patterned (r : positive) (R_numlimbs : nat)
           (NAB : Tuple.tuple Z R_numlimbs * (Tuple.tuple Z R_numlimbs * Tuple.tuple Z R_numlimbs))
  := do_pattern_strip (@add_cps r R_numlimbs (fst NAB) (fst (snd NAB)) (snd (snd NAB)) _ id).

Definition add_patterned_correct r R_numlimbs NAB
  : do_apply (add_patterned r R_numlimbs NAB)
    = @add_cps r R_numlimbs (fst NAB) (fst (snd NAB)) (snd (snd NAB)) _ id
  := eq_refl.

Definition compiled_preadd_sig (r : positive) (R_numlimbs : nat)
  : { t : _ & t }.
Proof.
  do_compile_sig
    (fun n T f NAB => @add_cps r n (fst NAB) (fst (snd NAB)) (snd (snd NAB)) T f)
    uconstr:(fun t xy => t R_numlimbs xy).
Defined.

Definition compiled_preadd' r R_numlimbs
  := Eval cbv [projT2 projT1 compiled_preadd_sig] in
      projT2 (compiled_preadd_sig r R_numlimbs).

Definition sub_patterned (r : positive) (R_numlimbs : nat)
           (NAB : Tuple.tuple Z R_numlimbs * (Tuple.tuple Z R_numlimbs * Tuple.tuple Z R_numlimbs))
  := do_pattern_strip (@sub_cps r R_numlimbs (fst NAB) (fst (snd NAB)) (snd (snd NAB)) _ id).

Definition sub_patterned_correct r R_numlimbs NAB
  : do_apply (sub_patterned r R_numlimbs NAB)
    = @sub_cps r R_numlimbs (fst NAB) (fst (snd NAB)) (snd (snd NAB)) _ id
  := eq_refl.

Definition compiled_presub_sig (r : positive) (R_numlimbs : nat)
  : { t : _ & t }.
Proof.
  do_compile_sig
    (fun n T f NAB => @sub_cps r n (fst NAB) (fst (snd NAB)) (snd (snd NAB)) T f)
    uconstr:(fun t xy => t R_numlimbs xy).
Defined.

Definition compiled_presub' r R_numlimbs
  := Eval cbv [projT2 projT1 compiled_presub_sig] in
      projT2 (compiled_presub_sig r R_numlimbs).

Definition opp_patterned (r : positive) (R_numlimbs : nat)
           (NA : Tuple.tuple Z R_numlimbs * Tuple.tuple Z R_numlimbs)
  := do_pattern_strip (@opp_cps r R_numlimbs (fst NA) (snd NA) _ id).

Definition opp_patterned_correct r R_numlimbs NA
  : do_apply (opp_patterned r R_numlimbs NA)
    = @opp_cps r R_numlimbs (fst NA) (snd NA) _ id
  := eq_refl.

Definition compiled_preopp_sig (r : positive) (R_numlimbs : nat)
  : { t : _ & t }.
Proof.
  do_compile_sig
    (fun n T f NA => @opp_cps r n (fst NA) (snd NA) T f)
    uconstr:(fun t xy => t R_numlimbs xy).
Defined.

Definition compiled_preopp' r R_numlimbs
  := Eval cbv [projT2 projT1 compiled_preopp_sig] in
      projT2 (compiled_preopp_sig r R_numlimbs).

Definition nonzero_patterned (R_numlimbs : nat)
           (A : Tuple.tuple Z R_numlimbs)
  := do_pattern_strip (@nonzero_cps R_numlimbs A _ id).

Definition nonzero_patterned_correct R_numlimbs A
  : do_apply (nonzero_patterned R_numlimbs A)
    = @nonzero_cps R_numlimbs A _ id
  := eq_refl.

Definition compiled_prenonzero_sig (R_numlimbs : nat)
  : { t : _ & t }.
Proof.
  do_compile_sig
    (fun n T (f : Tuple.tuple _ 1 -> _) A => @nonzero_cps n A T f)
    uconstr:(fun t xy => t R_numlimbs xy).
Defined.

Definition compiled_prenonzero' R_numlimbs
  := Eval cbv [projT2 projT1 compiled_prenonzero_sig] in
      projT2 (compiled_prenonzero_sig R_numlimbs).

Time Definition compiled_preadd := compiler_prered compiled_preadd'.
Time Definition compiled_presub := compiler_prered compiled_presub'.
Time Definition compiled_preopp := compiler_prered compiled_preopp'.
Time Definition compiled_prenonzero := compiler_prered compiled_prenonzero'.
Time Definition compiled_preredc := compiler_prered compiled_preredc'.

(*
Require Import NISTP256.AMD128.CurveParameters.
Require Import Specific.Framework.SynthesisFramework.

Locate Z.modinv_fueled.
Import RawCurveParameters.
Definition m := Eval vm_compute in (Z.to_pos (curve.(s) - Associational.eval curve.(c))).
Definition r := Eval vm_compute in (Z.to_pos (2^curve.(bitwidth))).
Definition r' : Z := Eval vm_compute in Option.invert_Some (ModInv.Z.modinv_fueled 10 (Z.pos r) (Z.pos m)).
Definition sz := Eval compute in curve.(sz).
Definition m_enc :=
  Eval compute in Base.m_enc' curve.(base) m sz.
Definition m' : Z := Eval vm_compute in Option.invert_Some (ModInv.Z.modinv_fueled 10 (-Z.pos m) (Z.pos r)).
Check Compilers.Syntax.interp_flat_type Z.Syntax.interp_base_type (Compilers.Syntax.tuple (Compilers.Syntax.Tbase Z.Syntax.TZ) 2%nat).
Import Compilers.Syntax.
Import Compilers.SmartMap.
Import ZExtended.Syntax.Util.
Import Z.Syntax.

Definition redc :=
  Eval cbv [m_enc  of_tupleZ Tuple.flat_interp_untuple Tuple.flat_interp_untuple'  fst snd Util.make_const  cast_const  interpToZ SmartVarfMap smart_interp_flat_map SmartPairf ZToInterp sz Syntax.tuple Syntax.tuple' lift_flat_type unextend_base_type domain codomain Linearize.Linearize Linearize.Linearize_gen Linearize.linearize_gen] in
    (option_map
       (fun v
        => Eta.ExprEta
             (Linearize.Linearize
             (fun var
              => Abs (fun xy => LetIn
                                  (let k : Compilers.Syntax.interp_flat_type Z.Syntax.interp_base_type (Tbase Z.Syntax.TZ ^ 2%nat) := (of_tupleZ (var := fun v => var (unextend_base_type v)) (n:=2) m_enc) in
                                   let k' := SmartPairf (SmartVarfMap (fun t v => Op (Z.Syntax.Util.make_const t v) TT) k) in
                                   k')
                                  (fun k'
                                   => ExprInversion.invert_Abs
                                        (T:=Arrow (Prod (Tbase TZ^2%nat) _) _)
                                        (v var) (k', xy))))))
       (compiled_preredc' r sz sz m')).
Timeout 30 Eval vm_compute in redc.
  in
  let x := (e
  eexists; exact x.
  Unshelve.
  pose unextend_base_type.
  SearchAbout Syntax.base_type base_type.
  exact var.
Defined.
*)
