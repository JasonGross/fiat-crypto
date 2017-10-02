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
  Time pose_mul synthesized mul.
  Show Ltac Profile.
  exact mul.
Time Defined.
