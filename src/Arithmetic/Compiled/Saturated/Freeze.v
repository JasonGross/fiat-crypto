Require Import Coq.ZArith.BinInt.
Require Import Crypto.Arithmetic.Saturated.Freeze.
Require Import Crypto.Arithmetic.Compiled.Compiler.

Definition compiled_prefreeze_sig (weight : nat -> Z) (n : nat) (mask : Z)
  : { t : _ & t }.
Proof.
  let freeze_cps := (eval cbv delta [freeze_cps] in freeze_cps) in
  do_compile_sig
    (fun n T f weight mask xy => @freeze_cps weight n mask (fst xy) (snd xy) T f)
    uconstr:(fun t xy => t n weight mask xy).
Defined.

Definition compiled_prefreeze' wt n mask
  := Eval cbv [projT2 projT1 compiled_prefreeze_sig] in
      projT2 (compiled_prefreeze_sig wt n mask).

Time Definition compiled_prefreeze := compiler_prered compiled_prefreeze'.
