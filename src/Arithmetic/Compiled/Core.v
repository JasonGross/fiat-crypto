Require Import Coq.ZArith.BinInt.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Compiled.Compiler.

Definition compiled_preadd_sig (weight : nat -> Z) (n : nat)
  : { t : _ & t }.
Proof.
  do_compile_sig
    (fun n T f weight xy => @Core.B.Positional.add_cps weight n (fst xy) (snd xy) T f)
    uconstr:(fun t xy => t n weight xy).
Defined.

Definition compiled_preadd' wt n
  := Eval cbv [projT2 projT1 compiled_preadd_sig] in
      projT2 (compiled_preadd_sig wt n).

Definition compiled_presub_sig (weight : nat -> Z) (n : nat)
  : { t : _ & t }.
Proof.
  do_compile_sig
    (fun n T f weight coef_xy => @Core.B.Positional.sub_cps weight n (fst coef_xy) (fst (snd coef_xy)) (snd (snd coef_xy)) T f)
    uconstr:(fun t xy => t n weight xy).
Defined.

Definition compiled_presub' wt n
  := Eval cbv [projT2 projT1 compiled_presub_sig] in
      projT2 (compiled_presub_sig wt n).

Definition compiled_preopp_sig (weight : nat -> Z) (n : nat)
  : { t : _ & t }.
Proof.
  do_compile_sig
    (fun n T f weight coef_x => @Core.B.Positional.opp_cps weight n (fst coef_x) (snd coef_x) T f)
    uconstr:(fun t x => t n weight x).
Defined.

Definition compiled_preopp' wt n
  := Eval cbv [projT2 projT1 compiled_preopp_sig] in
      projT2 (compiled_preopp_sig wt n).

Definition compiled_premul_sig (weight : nat -> Z) (n m : nat)
  : { t : _ & t }.
Proof.
  do_compile_sig
    (fun m T n f weight xy => @Core.B.Positional.mul_cps weight n m (fst xy) (snd xy) T f)
    uconstr:(fun t xy => t m n weight xy).
Defined.

Definition compiled_premul' wt n m
  := Eval cbv [projT2 projT1 compiled_premul_sig] in
      projT2 (compiled_premul_sig wt n m).

Definition compiled_prereduce_sig (weight : nat -> Z) (n m : nat) (s : Z) (c : list (Z * Z))
  : { t : _ & t }.
Proof.
  do_compile_sig
    (fun m T n f weight s c x => @Core.B.Positional.reduce_cps weight n m s c x T f)
    uconstr:(fun t x => t m n weight s c x).
Defined.

Definition compiled_prereduce' wt n m s c
  := Eval cbv [projT2 projT1 compiled_prereduce_sig] in
      projT2 (compiled_prereduce_sig wt n m s c).

Print Core.B.Positional.chained_carries_cps.
Definition compiled_prechained_carries_sig (weight : nat -> Z) (n : nat) (idxs : list nat)
  : { t : _ & t }.
Proof.
  do_compile_sig
    (fun n T f weight x => @Core.B.Positional.chained_carries_cps weight Core.modulo Core.div n x idxs T f)
    uconstr:(fun t x => t n weight x).
Defined.

Definition compiled_prechained_carries' wt n m s c
  := Eval cbv [projT2 projT1 compiled_prechained_carries_sig] in
      projT2 (compiled_prechained_carries_sig wt n m s c).

Definition compiled_precarry_reduce_sig (weight : nat -> Z) (n m : nat) (s : Z) (c : list (Z * Z))
  : { t : _ & t }.
Proof.
  do_compile_sig
    (fun m T n f weight s c x => @Core.B.Positional.carry_reduce_cps weight n m s c x T f)
    uconstr:(fun t x => t m n weight s c x).
Defined.

Definition compiled_precarry_reduce' wt n m s c
  := Eval cbv [projT2 projT1 compiled_precarry_reduce_sig] in
      projT2 (compiled_precarry_reduce_sig wt n m s c).

Time Definition compiled_preadd := compiler_prered compiled_preadd'.
Time Definition compiled_presub := compiler_prered compiled_presub'.
Time Definition compiled_preopp := compiler_prered compiled_preopp'.
Time Definition compiled_premul := compiler_prered compiled_premul'.
Time Definition compiled_prereduce := compiler_prered compiled_prereduce'.
Time Definition compiled_prechained_carries := compiler_prered compiled_prechained_carries'.
Time Definition compiled_precarry_reduce := compiler_prered compiled_precarry_reduce'.
