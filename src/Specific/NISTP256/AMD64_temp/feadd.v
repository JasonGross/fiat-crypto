Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Specific.NISTP256.AMD64_temp.Synthesis.

(* TODO : change this to field once field isomorphism happens *)
Definition add :
  { add : feBW -> feBW -> feBW
  | forall a b, phiBW (add a b) = F.add (phiBW a) (phiBW b) }.
Proof.
  Set Ltac Profiling.
  Time synthesize_add ().
  Show Ltac Profile.
Time Defined.

Print Assumptions add.
