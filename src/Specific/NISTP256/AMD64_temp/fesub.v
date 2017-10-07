Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Specific.NISTP256.AMD64_temp.Synthesis.

(* TODO : change this to field once field isomorphism happens *)
Definition sub :
  { sub : feBW -> feBW -> feBW
  | forall a b, phiBW (sub a b) = F.sub (phiBW a) (phiBW b) }.
Proof.
  Set Ltac Profiling.
  Time synthesize_sub ().
  Show Ltac Profile.
Time Defined.

Print Assumptions sub.
