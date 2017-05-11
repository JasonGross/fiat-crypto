(*** Word-By-Word Montgomery Multiplication Correctness *)
(** This file proves correctness of Montgomery Reduction and
    Montgomery Multiplication on [tuple ℤ]. *)
Require Import Coq.ZArith.ZArith Coq.micromega.Psatz.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.MontgomeryReduction.Definition.
Require Import Crypto.Arithmetic.MontgomeryReduction.Proofs.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Definition.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.BreakMatch.

Local Open Scope Z_scope.
Section columns.
  (** TODO(jadep): implement these *)
  Context (Columns_add_cps : forall (weight : nat -> Z)
                                    (n : nat)
                                    (a b : tuple (list Z) n)
                                    T
                                    (f : tuple (list Z) n -> T),
              T)
          (Columns_mul_cps : forall (weight : nat -> Z)
                                    (na nb m : nat)
                                    (a : tuple (list Z) na)
                                    (a : tuple (list Z) nb)
                                    T
                                    (f : tuple (list Z) m -> T),
              T).
  Context (modulo div : Z -> Z -> Z)
          (add_get_carry : Z -> Z -> Z -> Z * Z)
          (p_len : nat)
          (s : Z).
  Context (p : tuple Z p_len)
          (k0 : Z) (* [(-p⁻¹) mod 2ˢ] *).
  Local Notation weight := (fun i : nat => 2^(Z.of_nat i * s))%Z.
  Local Notation eval := (@B.Positional.eval weight _).
  Local Notation "x ≡ₚ y" := (Z.equiv_modulo (eval p) x y) : type_scope.
  Local Notation redc
    := (@redc Columns_add_cps Columns_mul_cps modulo div add_get_carry p_len s p k0).

  Lemma redc_correct count T (redcT := eval (redc count T))
        (HT : eval T < eval p)
    : redcT = eval T + if redcT >=? eval p
                       then eval p
                       else 0.
  Proof.
    subst redcT; induction count as [|count IHcount].
    { simpl in *.
      break_innermost_match; Z.ltb_to_lt; omega. }
    { simpl.
      rewrite IHcount.
      { admit. }
      { admit. } }
  Abort.
End columns.
