Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.HelperTactics.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.PoseTermWithName.
Require Import Crypto.Util.Tactics.CacheTerm.
Require Crypto.Util.Tuple.

Local Notation tuple := Tuple.tuple.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Infix "^" := tuple : type_scope.

Module Export Exports.
  Export Coq.setoid_ring.ZArithRing.
End Exports.

Ltac solve_constant_sig :=
  idtac;
  lazymatch goal with
  | [ |- { c : Z^?sz | Positional.Fdecode (m:=?M) ?wt c = ?v } ]
    => let t := (eval vm_compute in
                    (Positional.encode (n:=sz) (modulo:=modulo) (div:=div) wt (F.to_Z (m:=M) v))) in
       (exists t; vm_decide)
  end.

Section gen.
  Context (m : positive)
          (sz : nat)
          (s : Z)
          (c : list limb)
          (carry_chains : list (list nat))
          (sz_nonzero : sz <> 0%nat)
          (s_nonzero : s <> 0)
          (sz_le_log2_m : Z.of_nat sz <= Z.log2_up (Z.pos m))
          (m_correct : Z.pos m = s - Associational.eval c).

  (* Performs a full carry loop (as specified by carry_chain) *)
  Definition carry_sig'
    : { carry : (Z^sz -> Z^sz)%type
      | forall a : Z^sz,
          let eval := Positional.Fdecode (m := m) (wt_gen m sz) in
          eval (carry a) = eval a }.
  Proof.
    let a := fresh "a" in
    eexists; cbv beta zeta; intros a.
    pose proof (wt_gen0_1 m sz).
    pose proof (wt_gen_nonzero m sz); pose proof div_mod.
    pose proof (wt_gen_divides_chains m sz sz_nonzero sz_le_log2_m carry_chains).
    pose proof (wt_gen_divides' m sz sz_nonzero sz_le_log2_m).
    let wt := constr:(wt_gen m sz) in
    let x := constr:(chained_carries' sz wt s c a carry_chains) in
    F_mod_eq;
      transitivity (Positional.eval wt x); repeat autounfold;
        [|autorewrite with uncps push_id push_basesystem_eval ].
    Focus 2.
    { cbv [chained_carries'].
      change a with (id a) at 2.
      revert a; induction carry_chains as [|carry_chain carry_chains' IHcarry_chains];
        [ reflexivity | destruct_head_hnf' and ]; intros.
      rewrite step_chained_carries_cps'.
      destruct (length carry_chains') eqn:Hlenc.
      { destruct carry_chains'; [ | simpl in Hlenc; congruence ].
        destruct_head'_and;
          autorewrite with uncps push_id push_basesystem_eval;
          reflexivity. }
      { repeat autounfold;
          autorewrite with uncps push_id push_basesystem_eval.
        unfold chained_carries'.
        rewrite IHcarry_chains by auto.
        repeat autounfold; autorewrite with uncps push_id push_basesystem_eval.
        rewrite Positional.eval_carry by auto.
        rewrite Positional.eval_chained_carries by auto; reflexivity. } }
    Unfocus.
    cbv [mod_eq]; apply f_equal2; [|reflexivity];
      apply f_equal.
    reflexivity.
  Defined.
End gen.

Ltac pose_carry_sig sz m wt s c carry_chains sz_nonzero s_nonzero sz_le_log2_m m_correct carry_sig :=
  cache_sig_with_type_by
    {carry : (Z^sz -> Z^sz)%type |
     forall a : Z^sz,
       let eval := Positional.Fdecode (m := m) wt in
       eval (carry a) = eval a}
    ltac:(eexists; intros; etransitivity;
          [ apply f_equal
          | exact (proj2_sig (carry_sig' m sz s c carry_chains sz_nonzero s_nonzero sz_le_log2_m m_correct) _) ];
          cbv [proj1_sig carry_sig' chained_carries_cps' chained_carries_cps'_step];
          repeat autounfold;
          basesystem_partial_evaluation_RHS;
          reflexivity)
           carry_sig.

Ltac pose_zero_sig sz m wt zero_sig :=
  cache_term_with_type_by
    { zero : Z^sz | Positional.Fdecode (m:=m) wt zero = 0%F}
    solve_constant_sig
    zero_sig.

Ltac pose_one_sig sz m wt one_sig :=
  cache_term_with_type_by
    { one : Z^sz | Positional.Fdecode (m:=m) wt one = 1%F}
    solve_constant_sig
    one_sig.

Ltac pose_a24_sig sz m wt a24 a24_sig :=
  cache_term_with_type_by
    { a24t : Z^sz | Positional.Fdecode (m:=m) wt a24t = F.of_Z m a24 }
    solve_constant_sig
    a24_sig.

Ltac pose_add_sig sz m wt wt_nonzero add_sig :=
  cache_term_with_type_by
    { add : (Z^sz -> Z^sz -> Z^sz)%type |
      forall a b : Z^sz,
        let eval := Positional.Fdecode (m:=m) wt in
        eval (add a b) = (eval a + eval b)%F }
    ltac:(idtac;
          let a := fresh "a" in
          let b := fresh "b" in
          eexists; cbv beta zeta; intros a b;
          pose proof wt_nonzero;
          let x := constr:(
                     Positional.add_cps (n := sz) wt a b id) in
          solve_op_F wt x; reflexivity)
           add_sig.

Ltac pose_sub_sig sz m wt wt_nonzero coef sub_sig :=
  cache_term_with_type_by
    {sub : (Z^sz -> Z^sz -> Z^sz)%type |
     forall a b : Z^sz,
       let eval := Positional.Fdecode (m:=m) wt in
       eval (sub a b) = (eval a - eval b)%F}
    ltac:(idtac;
          let a := fresh "a" in
          let b := fresh "b" in
          eexists; cbv beta zeta; intros a b;
          pose proof wt_nonzero;
          let x := constr:(
                     Positional.sub_cps (n:=sz) (coef := coef) wt a b id) in
          solve_op_F wt x; reflexivity)
           sub_sig.

Ltac pose_opp_sig sz m wt wt_nonzero coef opp_sig :=
  cache_term_with_type_by
    {opp : (Z^sz -> Z^sz)%type |
     forall a : Z^sz,
       let eval := Positional.Fdecode (m := m) wt in
       eval (opp a) = F.opp (eval a)}
    ltac:(idtac;
          let a := fresh in
          eexists; cbv beta zeta; intros a;
          pose proof wt_nonzero;
          let x := constr:(
                     Positional.opp_cps (n:=sz) (coef := coef) wt a id) in
          solve_op_F wt x; reflexivity)
           opp_sig.


Ltac pose_mul_sig P_default_mul P_extra_prove_mul_eq sz m wt s c sz2 wt_nonzero mul_sig :=
  cache_term_with_type_by
    {mul : (Z^sz -> Z^sz -> Z^sz)%type |
     forall a b : Z^sz,
       let eval := Positional.Fdecode (m := m) wt in
       eval (mul a b) = (eval a * eval b)%F}
    ltac:(idtac;
          let a := fresh "a" in
          let b := fresh "b" in
          eexists; cbv beta zeta; intros a b;
          pose proof wt_nonzero;
          let x := constr:(
                     Positional.mul_cps (n:=sz) (m:=sz2) wt a b
                                        (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)) in
          solve_op_F wt x;
          P_default_mul ();
          P_extra_prove_mul_eq ();
          break_match; cbv [Let_In runtime_mul runtime_add]; repeat apply (f_equal2 pair); rewrite ?Z.shiftl_mul_pow2 by omega; ring)
           mul_sig.


Ltac pose_square_sig P_default_square P_extra_prove_square_eq sz m wt s c sz2 wt_nonzero square_sig :=
  cache_term_with_type_by
    {square : (Z^sz -> Z^sz)%type |
     forall a : Z^sz,
       let eval := Positional.Fdecode (m := m) wt in
       eval (square a) = (eval a * eval a)%F}
    ltac:(idtac;
          let a := fresh "a" in
          eexists; cbv beta zeta; intros a;
          pose proof wt_nonzero;
          let x := constr:(
                     Positional.mul_cps (n:=sz) (m:=sz2) wt a a
                                        (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)) in
          solve_op_F wt x;
          P_default_square ();
          P_extra_prove_square_eq ();
          break_match; cbv [Let_In runtime_mul runtime_add]; repeat apply (f_equal2 pair); rewrite ?Z.shiftl_mul_pow2 by omega; ring)
           square_sig.

Ltac pose_ring sz m wt wt_divides' sz_nonzero wt_nonzero zero_sig one_sig opp_sig add_sig sub_sig mul_sig ring :=
  cache_term
    (Ring.ring_by_isomorphism
       (F := F m)
       (H := Z^sz)
       (phi := Positional.Fencode wt)
       (phi' := Positional.Fdecode wt)
       (zero := proj1_sig zero_sig)
       (one := proj1_sig one_sig)
       (opp := proj1_sig opp_sig)
       (add := proj1_sig add_sig)
       (sub := proj1_sig sub_sig)
       (mul := proj1_sig mul_sig)
       (phi'_zero := proj2_sig zero_sig)
       (phi'_one := proj2_sig one_sig)
       (phi'_opp := proj2_sig opp_sig)
       (Positional.Fdecode_Fencode_id
          (sz_nonzero := sz_nonzero)
          (div_mod := div_mod)
          wt eq_refl wt_nonzero wt_divides')
       (Positional.eq_Feq_iff wt)
       (proj2_sig add_sig)
       (proj2_sig sub_sig)
       (proj2_sig mul_sig)
    )
    ring.

(*
Eval cbv [proj1_sig add_sig] in (proj1_sig add_sig).
Eval cbv [proj1_sig sub_sig] in (proj1_sig sub_sig).
Eval cbv [proj1_sig opp_sig] in (proj1_sig opp_sig).
Eval cbv [proj1_sig mul_sig] in (proj1_sig mul_sig).
Eval cbv [proj1_sig carry_sig] in (proj1_sig carry_sig).
 *)
