Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Specific.X25519.C64.ArithmeticSynthesisTest.
Require Import Crypto.Specific.ArithmeticSynthesisReflectiveFramework.
Import ArithmeticSynthesisFramework.Package.

(* TODO : change this to field once field isomorphism happens *)
Definition square :
  { square : feBW -> feBW
  | forall a, phiBW (square a) = F.mul (phiBW a) (phiBW a) }.
Proof.
  Set Ltac Profiling.
  Time pose_square synthesized square.
  Show Ltac Profile.
  exact square.
Time Defined.
