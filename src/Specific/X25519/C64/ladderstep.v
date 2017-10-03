Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Specific.X25519.C64.ArithmeticSynthesisTest.
Require Import Crypto.Specific.ArithmeticSynthesisReflectiveFrameworkLadderstep.
Import ArithmeticSynthesisFramework.Package.

(* TODO : change this to field once field isomorphism happens *)
Definition xzladderstep :
  { xzladderstep : feW -> feW * feW -> feW * feW -> feW * feW * (feW * feW)
  | forall x1 Q Q',
      let xz := xzladderstep x1 Q Q' in
      let eval := B.Positional.Fdecode wt in
      feW_bounded x1
      -> feW_bounded (fst Q) /\ feW_bounded (snd Q)
      -> feW_bounded (fst Q') /\ feW_bounded (snd Q')
      -> ((feW_bounded (fst (fst xz)) /\ feW_bounded (snd (fst xz)))
          /\ (feW_bounded (fst (snd xz)) /\ feW_bounded (snd (snd xz))))
         /\ Tuple.map (n:=2) (Tuple.map (n:=2) phiW) xz = FMxzladderstep _ (eval (proj1_sig a24_sig)) (phiW x1) (Tuple.map (n:=2) phiW Q) (Tuple.map (n:=2) phiW Q') }.
Proof.
  Set Ltac Profiling.
  (*
  Time assert_xzladderstep_then synthesized xzladderstep
       ltac:(preglue_xzladderstep synthesized).
  Time Glue.refine_to_reflective_glue (64::128::nil)%nat%list.
  Import Pipeline.
  Time ReflectiveTactics.refine_with_pipeline_correct default.
  { Time ReflectiveTactics.do_reify. }
  { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
  { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
  { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
  { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
  { Time UnifyAbstractReflexivity.unify_abstract_vm_compute_rhs_reflexivity. }
  { Time UnifyAbstractReflexivity.unify_abstract_rhs_reflexivity. }
  { Time ReflectiveTactics.unify_abstract_renamify_rhs_reflexivity. }
  { Time SubstLet.subst_let; clear; abstract vm_cast_no_check (eq_refl true). }
  { Time SubstLet.subst_let; clear; vm_compute; reflexivity. }
  { Time UnifyAbstractReflexivity.unify_abstract_compute_rhs_reflexivity. }
  { Time ReflectiveTactics.unify_abstract_cbv_interp_rhs_reflexivity. }
  { Time abstract ReflectiveTactics.handle_bounds_from_hyps. }
  { Time abstract ReflectiveTactics.handle_boundedness_side_condition. }
  *)
  Time pose_xzladderstep synthesized xzladderstep.
  Show Ltac Profile.
  exact xzladderstep.
Time Defined.
