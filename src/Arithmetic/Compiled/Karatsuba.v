Require Import Coq.ZArith.BinInt.
Require Import Crypto.Arithmetic.KaratsubaUnfolder.
Require Import Crypto.Arithmetic.Karatsuba.
Require Import Crypto.Arithmetic.Compiled.Compiler.

Definition karatsuba_mul_patterned (weight : nat -> Z) (n n2 : nat) (s : Z) (xy : Tuple.tuple Z n2 * Tuple.tuple Z n2)
  := do_pattern_strip (@karatsuba_mul_cps weight n n2 s (fst xy) (snd xy) _ id).

Definition karatsuba_mul_patterned_correct wt n n2 s xy
  : do_apply (karatsuba_mul_patterned wt n n2 s xy)
    = @karatsuba_mul_cps wt n n2 s (fst xy) (snd xy) _ id
  := eq_refl.

Definition compiled_prekaratsuba_mul_sig (weight : nat -> Z) (n n2 : nat) (s : Z)
  : { t : _ & t }.
Proof.
  let karatsuba_mul_cps := (eval cbv delta [karatsuba_mul_cps] in karatsuba_mul_cps) in
  do_compile_sig
    (fun n2 T f n weight s xy => @karatsuba_mul_cps weight n n2 s (fst xy) (snd xy) T f)
    uconstr:(fun t xy => t n2 n weight s xy).
Defined.

Definition compiled_prekaratsuba_mul' wt n n2 s
  := Eval cbv [projT2 projT1 compiled_prekaratsuba_mul_sig] in
      projT2 (compiled_prekaratsuba_mul_sig wt n n2 s).

Definition goldilocks_mul_patterned (weight : nat -> Z) (n n2 : nat) (s : Z) (xy : Tuple.tuple Z n2 * Tuple.tuple Z n2)
  := do_pattern_strip (@goldilocks_mul_cps weight n n2 s (fst xy) (snd xy) _ id).

Definition goldilocks_mul_patterned_correct wt n n2 s xy
  : do_apply (goldilocks_mul_patterned wt n n2 s xy)
    = @goldilocks_mul_cps wt n n2 s (fst xy) (snd xy) _ id
  := eq_refl.

Definition compiled_pregoldilocks_mul_sig (weight : nat -> Z) (n n2 : nat) (s : Z)
  : { t : _ & t }.
Proof.
  let goldilocks_mul_cps := (eval cbv delta [goldilocks_mul_cps] in goldilocks_mul_cps) in
  do_compile_sig
    (fun n2 n T f weight s xy => @goldilocks_mul_cps weight n n2 s (fst xy) (snd xy) T f)
    uconstr:(fun t xy => t n2 n weight s xy).
Defined.

Definition compiled_pregoldilocks_mul' wt n n2 s
  := Eval cbv [projT2 projT1 compiled_pregoldilocks_mul_sig] in
      projT2 (compiled_pregoldilocks_mul_sig wt n n2 s).

Time Definition compiled_prekaratsuba_mul := compiler_prered compiled_prekaratsuba_mul'.
Time Definition compiled_pregoldilocks_mul := compiler_prered compiled_pregoldilocks_mul'.
