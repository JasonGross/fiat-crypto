Require Import Coq.ZArith.BinInt.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Definition.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Proofs.
Require Import Crypto.Arithmetic.Core. Import B.
Require Crypto.Arithmetic.Saturated.MontgomeryAPI.
Require Import Crypto.Arithmetic.Compiled.Compiler.

Hint Unfold
     redc_cps
     pre_redc_cps
     redc_loop_cps
     redc_body_cps
     MontgomeryAPI.T
     MontgomeryAPI.zero
     MontgomeryAPI.nonzero_cps
     MontgomeryAPI.join0_cps
     MontgomeryAPI.divmod_cps
     MontgomeryAPI.drop_high_cps
     MontgomeryAPI.scmul_cps
     MontgomeryAPI.add_cps
     MontgomeryAPI.add_S1_cps
     MontgomeryAPI.add_S2_cps
     MontgomeryAPI.sub_then_maybe_add_cps
     MontgomeryAPI.conditional_sub_cps
     UniformWeight.uweight
  : basesystem_partial_evaluation_unfolder.

Definition compiled_preredc_sig (r : positive) (R_numlimbs : nat)
           (A_numlimbs : nat) (k : Z)
  : { t : _ & t }.
Proof.
  do_compile_sig
    (fun n m T (f : Tuple.tuple _ _ -> _) (NAB : Tuple.tuple _ _ * (Tuple.tuple _ _ * Tuple.tuple _ _)) k => @redc_cps r n (fst NAB) m (fst (snd NAB)) (snd (snd NAB)) k T f)
    uconstr:(fun t xy => t R_numlimbs A_numlimbs xy k).
Defined.
