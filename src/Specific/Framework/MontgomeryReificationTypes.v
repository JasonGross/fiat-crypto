Require Import Coq.ZArith.ZArith.
Require Import Coq.romega.ROmega.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.ZRange Crypto.Util.BoundedWord.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Decidable.

Require Crypto.Arithmetic.Saturated.MontgomeryAPI.

Notation meval_type feBW :=
  (feBW -> Z)
    (only parsing).

Ltac solve_meval r :=
  lazymatch goal with
  | [ |- meval_type ?feBW ]
    => exact (fun x : feBW => MontgomeryAPI.eval (Z.pos r) (BoundedWordToZ _ _ _ x))
  end.

Ltac solve_feBW_small sz feBW meval r m_enc :=
  exact
    { v : feBW | meval v < MontgomeryAPI.eval (n:=sz) (Z.pos r) m_enc }
.

Notation feBW_of_feBW_small_type feBW feBW_small :=
  (feBW_small -> feBW)
    (only parsing).

Ltac solve_feBW_of_feBW_small :=
  lazymatch goal with
  | [ |- feBW_of_feBW_small_type ?feBW ?feBW_small ]
    => refine (@proj1_sig _ _)
  end.

Notation phiM_type feBW m :=
  (feBW -> F m)
    (only parsing).

Ltac solve_phiM meval montgomery_to_F :=
  lazymatch goal with
  | [ |- phiM_type ?feBW ?m ]
    => exact (fun x : feBW => montgomery_to_F (meval x))
  end.

Notation phiM_small_type feBW_small m :=
  (feBW_small -> F m)
    (only parsing).

Ltac solve_phiM_small feBW_of_feBW_small meval montgomery_to_F :=
  lazymatch goal with
  | [ |- phiM_small_type ?feBW_small ?m ]
    => exact (fun x : feBW_small => montgomery_to_F (meval (feBW_of_feBW_small x)))
  end.
