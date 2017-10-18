Require Import Coq.ZArith.BinInt.
Require Import Crypto.Arithmetic.CoreUnfolder.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Compiled.Compiler.

Definition add_patterned (weight : nat -> Z) (n : nat) (xy : Tuple.tuple Z n * Tuple.tuple Z n)
  := do_pattern_strip (@Core.B.Positional.add_cps weight n (fst xy) (snd xy) _ id).

Definition add_patterned_correct wt n xy
  : do_apply (add_patterned wt n xy)
    = @Core.B.Positional.add_cps wt n (fst xy) (snd xy) _ id
  := eq_refl.

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

Definition sub_patterned (weight : nat -> Z) (n : nat) (coef_xy : Tuple.tuple Z n * (Tuple.tuple Z n * Tuple.tuple Z n))
  := do_pattern_strip (@Core.B.Positional.sub_cps weight n (fst coef_xy) (fst (snd coef_xy)) (snd (snd coef_xy)) _ id).

Definition sub_patterned_correct wt n coef_xy
  : do_apply (sub_patterned wt n coef_xy)
    = @Core.B.Positional.sub_cps wt n (fst coef_xy) (fst (snd coef_xy)) (snd (snd coef_xy)) _ id
  := eq_refl.

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

Definition opp_patterned (weight : nat -> Z) (n : nat) (coef_x : Tuple.tuple Z n * Tuple.tuple Z n)
  := do_pattern_strip (@Core.B.Positional.opp_cps weight n (fst coef_x) (snd coef_x) _ id).

Definition opp_patterned_correct wt n coef_x
  : do_apply (opp_patterned wt n coef_x)
    = @Core.B.Positional.opp_cps wt n (fst coef_x) (snd coef_x) _ id
  := eq_refl.

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

Definition mul_patterned (weight : nat -> Z) (n m : nat) (xy : Tuple.tuple Z n * Tuple.tuple Z n)
  := do_pattern_strip (@Core.B.Positional.mul_cps weight n m (fst xy) (snd xy) _ id).

Definition mul_patterned_correct wt n m xy
  : do_apply (mul_patterned wt n m xy)
    = @Core.B.Positional.mul_cps wt n m (fst xy) (snd xy) _ id
  := eq_refl.

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

Definition reduce_patterned (weight : nat -> Z) (m n : nat) (s : Z) (c : list (Z * Z)) (x : Tuple.tuple Z m)
  := do_pattern_strip (@Core.B.Positional.reduce_cps weight m n s c x _ id).

Definition reduce_patterned_correct wt m n s c x
  : do_apply (reduce_patterned wt m n s c x)
    = @Core.B.Positional.reduce_cps wt m n s c x _ id
  := eq_refl.

Definition compiled_prereduce_sig (weight : nat -> Z) (m n : nat) (s : Z) (c : list (Z * Z))
  : { t : _ & t }.
Proof.
  do_compile_sig
    (fun n T m f weight s c x => @Core.B.Positional.reduce_cps weight m n s c x T f)
    uconstr:(fun t x => t n m weight s c x).
Defined.

Definition compiled_prereduce' wt m n s c
  := Eval cbv [projT2 projT1 compiled_prereduce_sig] in
      projT2 (compiled_prereduce_sig wt m n s c).

Definition chained_carries_patterned (weight : nat -> Z) (n : nat) (idxs : list nat) (x : Tuple.tuple Z n)
  := do_pattern_strip (Core.B.Positional.chained_carries_cps weight (modulo_cps:=@Core.modulo_cps) (div_cps:=@Core.div_cps) (n:=n) x idxs id).

Definition chained_carries_patterned_correct wt n idxs x
  : do_apply (chained_carries_patterned wt n idxs x)
    = Core.B.Positional.chained_carries_cps wt (modulo_cps:=@Core.modulo_cps) (div_cps:=@Core.div_cps) (n:=n) x idxs id
  := eq_refl.

Definition compiled_prechained_carries_sig (weight : nat -> Z) (n : nat) (idxs : list nat)
  : { t : _ & t }.
Proof.
  do_compile_sig
    (fun n T f weight x => Core.B.Positional.chained_carries_cps weight (modulo_cps:=@Core.modulo_cps) (div_cps:=@Core.div_cps) (n:=n) x idxs (T:=T) f)
    uconstr:(fun t x => t n weight x).
Defined.

Definition compiled_prechained_carries' wt n idxs
  := Eval cbv [projT2 projT1 compiled_prechained_carries_sig] in
      projT2 (compiled_prechained_carries_sig wt n idxs).

Definition chained_carries_reduce_patterned (weight : nat -> Z) (n : nat) (s : Z) (c : list (Z * Z)) (idxs : list (list nat)) (x : Tuple.tuple Z n)
  := do_pattern_strip (Core.B.Positional.chained_carries_reduce_cps weight (modulo_cps:=@Core.modulo_cps) (div_cps:=@Core.div_cps) (n:=n) s c x idxs id).

Definition chained_carries_reduce_patterned_correct wt n s c idxs x
  : do_apply (chained_carries_reduce_patterned wt n s c idxs x)
    = Core.B.Positional.chained_carries_reduce_cps wt (modulo_cps:=@Core.modulo_cps) (div_cps:=@Core.div_cps) (n:=n) s c x idxs id
  := eq_refl.

Definition compiled_prechained_carries_reduce_sig (weight : nat -> Z) (n : nat) (s : Z) (c : list (Z * Z)) (idxs : list (list nat))
  : { t : _ & t }.
Proof.
  do_compile_sig
    (fun n T f weight s c x => Core.B.Positional.chained_carries_reduce_cps weight (modulo_cps:=@Core.modulo_cps) (div_cps:=@Core.div_cps) (n:=n) s c x idxs (T:=T) f)
    uconstr:(fun t x => t n weight s c x).
Defined.

Definition compiled_prechained_carries_reduce' wt n s c idxs
  := Eval cbv [projT2 projT1 compiled_prechained_carries_reduce_sig] in
      projT2 (compiled_prechained_carries_reduce_sig wt n s c idxs).

Definition carry_reduce_patterned (weight : nat -> Z) (n : nat) (s : Z) (c : list (Z * Z)) (x : Tuple.tuple Z n)
  := do_pattern_strip (Core.B.Positional.carry_reduce_cps weight (modulo_cps:=@Core.modulo_cps) (div_cps:=@Core.div_cps) (n:=n) s c x id).

Definition carry_reduce_patterned_correct wt n s c x
  : do_apply (carry_reduce_patterned wt n s c x)
    = Core.B.Positional.carry_reduce_cps wt (modulo_cps:=@Core.modulo_cps) (div_cps:=@Core.div_cps) (n:=n) s c x id
  := eq_refl.

Definition compiled_precarry_reduce_sig (weight : nat -> Z) (n : nat) (s : Z) (c : list (Z * Z))
  : { t : _ & t }.
Proof.
  do_compile_sig
    (fun n T f weight s c x => Core.B.Positional.carry_reduce_cps weight (n:=n) (div_cps:=@Core.div_cps) (modulo_cps:=@Core.modulo_cps) s c x (T:=T) f)
    uconstr:(fun t x => t n weight s c x).
Defined.

Definition compiled_precarry_reduce' wt n s c
  := Eval cbv [projT2 projT1 compiled_precarry_reduce_sig] in
      projT2 (compiled_precarry_reduce_sig wt n s c).

Time Definition compiled_preadd := compiler_prered compiled_preadd'.
Time Definition compiled_presub := compiler_prered compiled_presub'.
Time Definition compiled_preopp := compiler_prered compiled_preopp'.
Time Definition compiled_premul := compiler_prered compiled_premul'.
Time Definition compiled_prereduce := compiler_prered compiled_prereduce'.
Time Definition compiled_prechained_carries := compiler_prered compiled_prechained_carries'.
Time Definition compiled_prechained_carries_reduce := compiler_prered compiled_prechained_carries_reduce'.
Time Definition compiled_precarry_reduce := compiler_prered compiled_precarry_reduce'.
