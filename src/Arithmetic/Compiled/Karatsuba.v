Require Import Coq.ZArith.BinInt.
Require Import Crypto.Arithmetic.Karatsuba.
Require Import Crypto.Arithmetic.Compiled.Compiler.

Definition compiled_prekaratsuba_mul_sig (weight : nat -> Z) (n m : nat) (s : Z)
  : { t : _ & t }.
Proof.
  let karatsuba_mul_cps := (eval cbv delta [karatsuba_mul_cps] in karatsuba_mul_cps) in
  do_compile_sig
    (fun n T f m weight s xy => @karatsuba_mul_cps weight m n s (fst xy) (snd xy) T f)
    uconstr:(fun t xy => t n m weight s xy).
Defined.

Definition compiled_prekaratsuba_mul' wt n m s
  := Eval cbv [projT2 projT1 compiled_prekaratsuba_mul_sig] in
      projT2 (compiled_prekaratsuba_mul_sig wt n m s).

Definition compiled_pregoldilocks_mul_sig (weight : nat -> Z) (n m : nat) (s : Z)
  : { t : _ & t }.
Proof.
  let goldilocks_mul_cps := (eval cbv delta [goldilocks_mul_cps] in goldilocks_mul_cps) in
  do_compile_sig
    (fun n m T f weight s xy => @goldilocks_mul_cps weight m n s (fst xy) (snd xy) T f)
    uconstr:(fun t xy => t n m weight s xy).
Defined.

Definition compiled_pregoldilocks_mul' wt n m s
  := Eval cbv [projT2 projT1 compiled_pregoldilocks_mul_sig] in
      projT2 (compiled_pregoldilocks_mul_sig wt n m s).

Time Definition compiled_prekaratsuba_mul := compiler_prered compiled_prekaratsuba_mul'.
Time Definition compiled_pregoldilocks_mul := compiler_prered compiled_pregoldilocks_mul'.
