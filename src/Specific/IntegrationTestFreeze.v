Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Specific.X25519.C64.ArithmeticSynthesisTest.
Require Import Crypto.Specific.ArithmeticSynthesisReflectiveFramework.
Import ArithmeticSynthesisFramework.Package.

(* TODO : change this to field once field isomorphism happens *)
Definition freeze :
  { freeze : feBW -> feBW
  | forall a, phiBW (freeze a) = phiBW a }.
Proof.
  Set Ltac Profiling.
  Time pose_freeze synthesized freeze.
  Show Ltac Profile.
  exact freeze.
Time Defined.
