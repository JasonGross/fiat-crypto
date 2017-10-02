Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Specific.X25519.C64.ArithmeticSynthesisTest.
Require Import Crypto.Specific.ArithmeticSynthesisReflectiveFramework.
Import ArithmeticSynthesisFramework.Package.

(* TODO : change this to field once field isomorphism happens *)
Definition sub :
  { sub : feBW -> feBW -> feBW
  | forall a b, phiBW (sub a b) = F.sub (phiBW a) (phiBW b) }.
Proof.
  Set Ltac Profiling.
  Time pose_sub synthesized sub.
  Show Ltac Profile.
  exact sub.
Time Defined.
