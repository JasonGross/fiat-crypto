Require Import Coq.ZArith.BinInt.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Definition.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Proofs.
Require Import Crypto.Arithmetic.Core. Import B.
Require Crypto.Arithmetic.Saturated.MontgomeryAPI.
Require Import Crypto.Arithmetic.Compiled.Compiler.

Hint Unfold
     redc_cps
     MontgomeryAPI.conditional_sub_cps
     MontgomeryAPI.T
     MontgomeryAPI.drop_high_cps
  : basesystem_partial_evaluation_unfolder.

Definition compiled_preredc_sig (r : positive) (R_numlimbs : nat)
           (A_numlimbs : nat) (k : Z)
  : { t : _ & t }.
Proof.
  do_compile_sig
    (fun n m T (f : Tuple.tuple _ _ -> _) (NAB : Tuple.tuple _ _ * (Tuple.tuple _ _ * Tuple.tuple _ _)) k => @redc_cps r n (fst NAB) m (fst (snd NAB)) (snd (snd NAB)) k T f)
    uconstr:(fun t xy => t R_numlimbs A_numlimbs xy k).
Defined.
