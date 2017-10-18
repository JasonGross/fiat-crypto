Require Import Coq.ZArith.BinInt.
Require Import Crypto.Arithmetic.Saturated.FreezeUnfolder.
Require Import Crypto.Arithmetic.Saturated.Freeze.
Require Import Crypto.Arithmetic.Compiled.Compiler.

Definition freeze_patterned (weight : nat -> Z) (n : nat) (mask : Z) (xy : Tuple.tuple Z n * Tuple.tuple Z n)
  := do_pattern_strip (@freeze_cps weight n mask (fst xy) (snd xy) _ id).

Definition freeze_patterned_correct wt n mask xy
  : do_apply (freeze_patterned wt n mask xy)
    = @freeze_cps wt n mask (fst xy) (snd xy) _ id
  := eq_refl.

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
