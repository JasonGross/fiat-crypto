Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.HelperTactics.
Require Import Crypto.Util.QUtil.
Require Import Crypto.Util.Decidable.
Require Crypto.Util.Tuple.

  (* emacs for adjusting definitions *)
  (* Query replace regexp (default Definition \([a-zA-Z_0-9]+\) : \([A-Za-z0-9_]+\) := P.compute \(.*\)\.\(.*\) -> Ltac pose_\1 \1 :=\4^J  cache_term_with_type_by^J      \2^J      ltac:(let v := P.do_compute \3 in exact v)^J      \1.):  *)
  (* Query replace regexp (default Definition \([a-zA-Z_0-9]+\) : \([A-Za-z0-9_]+\) := P.compute \(.*\)\.\(.*\) -> Ltac pose_\1 \1 :=\4^J  cache_term_with_type_by^J      \2^J      ltac:(let v := P.do_compute \3 in exact v)^J      \1.):  *)
  (* Query replace regexp (default Definition \([a-zA-Z_0-9]+\) : \([A-Za-z0-9_ \.]*\) := P.compute \(.*\)\.\(.*\) -> Ltac pose_\1 \1 :=\4^J  cache_term_with_type_by^J      (\2)^J      ltac:(let v := P.do_compute \3 in exact v)^J      \1.): *)
  (* Query replace regexp (default Definition \([a-zA-Z_0-9]+\) := P.compute \(.*\)\.\(.*\) -> Ltac pose_\1 \1 :=\3^J  let v := P.do_compute \2 in cache_term v \1.):  *)

Notation r_type :=
  positive
    (only parsing).
Ltac solve_r bitwidth :=
  lazymatch goal with
  | [ |- r_type ]
    => let v := (eval vm_compute in (Z.to_pos (2^bitwidth))) in exact v
  end.

Ltac solve_m s c := (* modulus *)
  let v := (eval vm_compute in (Z.to_pos (s - Associational.eval c))) in
  exact v.

Section wt.
  Import QArith Qround.
  Local Coercion QArith_base.inject_Z : Z >-> Q.
  Local Coercion Z.of_nat : nat >-> Z.
  Local Coercion Z.pos : positive >-> Z.
  Definition wt_gen (m : positive) (sz : nat) (i:nat) : Z := 2^Qceiling((Z.log2_up m/sz)*i).
End wt.
Ltac solve_wt m sz :=
  let v := (eval cbv [wt_gen] in (wt_gen m sz)) in
  exact v.

Ltac solve_sz2 sz :=
  let v := (eval vm_compute in ((sz * 2) - 1)%nat) in
  exact v.

Ltac solve_half_sz sz :=
  let v := (eval compute in (sz / 2)%nat) in
  exact v.

Notation half_sz_nonzero_prop half_sz :=
  (half_sz <> 0%nat)
    (only parsing).
Ltac solve_half_sz_nonzero :=
  lazymatch goal with
  | [ |- half_sz_nonzero_prop ?half_sz ]
    => cbv; congruence
  end.

Ltac solve_m_enc sz s c wt :=
  let v := (eval vm_compute in (Positional.encode (modulo:=modulo) (div:=div) (n:=sz) wt (s-Associational.eval c))) in
  let v := (eval compute in v) in (* compute away the type arguments *)
  exact v.
Ltac solve_coef sz wt m_enc coef_div_modulus := (* subtraction coefficient *)
  let v := (eval vm_compute in
               ((fix addm (acc: Z^sz) (ctr : nat) : Z^sz :=
                   match ctr with
                   | O => acc
                   | S n => addm (Positional.add_cps wt acc m_enc id) n
                   end) (Positional.zeros sz) coef_div_modulus)) in
  exact v.

Notation coef_mod_type m sz wt coef :=
  (mod_eq m (Positional.eval (n:=sz) wt coef) 0)
    (only parsing).
Ltac solve_coef_mod :=
  lazymatch goal with
  | [ |- coef_mod_type ?m ?sz ?wt ?coef ]
    => exact eq_refl
  end.
Notation sz_nonzero_prop sz :=
  (sz <> 0%nat)
    (only parsing).
Ltac solve_sz_nonzero :=
  lazymatch goal with
  | [ |- sz_nonzero_prop ?sz ]
    => vm_decide_no_check
  end.
Notation wt_nonzero_prop wt :=
  (forall i, wt i <> 0)
    (only parsing).
Ltac solve_wt_nonzero :=
  lazymatch goal with
  | [ |- wt_nonzero_prop ?wt ]
    => eapply pow_ceil_mul_nat_nonzero; vm_decide_no_check
  end.
Notation wt_nonneg_prop wt :=
  (forall i, 0 <= wt i)
    (only parsing).
Ltac solve_wt_nonneg :=
  lazymatch goal with
  | [ |- wt_nonneg_prop ?wt ]
    => apply pow_ceil_mul_nat_nonneg; vm_decide_no_check
  end.
Notation wt_divides_prop wt :=
  (forall i, wt (S i) / wt i > 0)
    (only parsing).
Ltac solve_wt_divides :=
  lazymatch goal with
  | [ |- wt_divides_prop ?wt ]
    => apply pow_ceil_mul_nat_divide; vm_decide_no_check
  end.
Notation wt_divides'_prop wt :=
  (forall i, wt (S i) / wt i <> 0)
    (only parsing).
Ltac solve_wt_divides' wt_divides :=
  lazymatch goal with
  | [ |- wt_divides'_prop ?wt ]
    => symmetry; apply Z.lt_neq, Z.gt_lt_iff, wt_divides
  end.
Local Notation wt_divides_chain_type_part carry_chain wt :=
  (forall i (H:In i carry_chain), wt (S i) / wt i <> 0)
    (only parsing).

Fixpoint wt_divides_chains_type'
         (carry_chains : list (list nat))
         (wt : nat -> Z)
  : Prop
  := match carry_chains with
     | nil
       => True
     | carry_chain :: nil
       => wt_divides_chain_type_part carry_chain wt
     | carry_chain :: carry_chains
       => (wt_divides_chain_type_part carry_chain wt
           * wt_divides_chains_type' carry_chains wt)
     end.
Ltac helper_solve_wt_divides_chain wt carry_chain wt_divides' wt_divides_chain :=
  refine (_ : forall i (H:In i carry_chain), wt (S i) / wt i <> 0);
  let i := fresh "i" in intros i ?; exact (wt_divides' i).
Ltac internal_solve_wt_divides_chains' wt carry_chains wt_divides' :=
  lazymatch carry_chains with
  | ?carry_chain :: nil
    => helper_solve_wt_divides_chain wt carry_chain wt_divides'
  | ?carry_chain :: ?carry_chains
    => refine ((_, _));
       [ helper_solve_wt_divides_chain wt carry_chain wt_divides'
       | internal_solve_wt_divides_chains' wt carry_chains wt_divides' ]
  end.
Notation wt_divides_chains_type carry_chains wt :=
  (wt_divides_chains_type' carry_chains wt)
    (only parsing).
Ltac solve_wt_divides_chains wt carry_chains wt_divides' :=
  let carry_chains := (eval cbv delta [carry_chains] in carry_chains) in
  internal_solve_wt_divides_chains' wt carry_chains wt_divides'.

Notation wt_pos_prop wt :=
  (forall i, wt i > 0)
    (only parsing).
Ltac solve_wt_pos :=
  lazymatch goal with
  | [ |- wt_pos_prop ?wt ]
    => eapply pow_ceil_mul_nat_pos; vm_decide_no_check
  end.

Notation wt_multiples_prop wt :=
  (forall i, wt (S i) mod (wt i) = 0)
    (only parsing).
Ltac solve_wt_multiples :=
  lazymatch goal with
  | [ |- wt_multiples_prop ?wt ]
    => apply pow_ceil_mul_nat_multiples; vm_decide_no_check
  end.
