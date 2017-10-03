Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Specific.X25519.C32.ArithmeticSynthesisTest.
Require Import Crypto.Specific.ArithmeticSynthesisReflectiveFramework.
Import ArithmeticSynthesisFramework.Package.

(* TODO : change this to field once field isomorphism happens *)
Definition mul :
  { mul : feBW -> feBW -> feBW
  | forall a b, phiBW (mul a b) = F.mul (phiBW a) (phiBW b) }.
Proof.
  Set Ltac Profiling.
  (*
  Require Import Crypto.Compilers.Z.Bounds.Pipeline.
  Require Import Crypto.Specific.ArithmeticSynthesisFramework.
  Time assert_mul_then_preglue synthesized mul.
  Time Glue.refine_to_reflective_glue (64::128::nil)%nat%list.
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
  Time pose_mul synthesized mul.
  Show Ltac Profile.
  exact mul.
Time Defined.
