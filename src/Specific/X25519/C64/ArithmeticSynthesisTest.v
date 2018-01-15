Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Arithmetic.Saturated.Freeze.
Require Crypto.Specific.CurveParameters.
Require Import Crypto.Specific.X25519.C64.CurveParameters.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Crypto.Util.Tuple.
Require Import Crypto.Util.QUtil.
Local Notation tuple := Tuple.tuple.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

Module P := CurveParameters.FillCurveParameters Curve.

Section Ops.
  Local Infix "^" := tuple : type_scope.

  (* These definitions will need to be passed as Ltac arguments (or
  cleverly inferred) when things are eventually automated *)
  Definition sz : nat := 5.
  Definition bitwidth : Z := P.compute P.bitwidth.
  Definition s : Z := 2^256. (* don't want to compute, e.g., [2^255] *)
  Definition c : list B.limb := [(1,2^32 + 977)].
  Definition carry_chain1 := [0;1;2;3;4;0]%nat.
  Definition carry_chain2 := [0;1;2;3;4;0]%nat.

  Definition a24 := P.compute P.a24.
  Definition coef_div_modulus : nat := P.compute P.coef_div_modulus.
  (* These definitions are inferred from those above *)
  Definition m := Eval vm_compute in Z.to_pos (s - Associational.eval c). (* modulus *)
  Section wt.
    Import QArith Qround.
    Local Coercion QArith_base.inject_Z : Z >-> Q.
    Definition wt (i:nat) : Z := match i with
                                 | 0 => 52
                                 | 1 => 52
                                 | 2 => 52
                                 | 3 => 52
                                 | 4 => 48
                                 | _ => 0
                                 end%nat.
  End wt.
  Definition sz2 := Eval vm_compute in ((sz * 2) - 1)%nat.
  Definition m_enc :=
    Eval vm_compute in (Positional.encode (modulo:=modulo) (div:=div) (n:=sz) wt (s-Associational.eval c)).
  Definition coef := (* subtraction coefficient *)
    Eval vm_compute in
      ((fix addm (acc: Z^sz) (ctr : nat) : Z^sz :=
         match ctr with
         | O => acc
         | S n => addm (Positional.add_cps wt acc m_enc id) n
        end) (Positional.zeros sz) coef_div_modulus).
  Definition coef_mod : mod_eq m (Positional.eval (n:=sz) wt coef) 0 := eq_refl.
  Lemma sz_nonzero : sz <> 0%nat. Proof. vm_decide. Qed.
  Lemma wt_nonzero i : wt i <> 0. Admitted.
  (*Proof. eapply pow_ceil_mul_nat_nonzero; vm_decide. Qed.*)
  Lemma wt_nonneg i : 0 <= wt i. Admitted.
  (*Proof. apply pow_ceil_mul_nat_nonneg; vm_decide. Qed.*)
  Lemma wt_divides i : wt (S i) / wt i > 0. Admitted.
  (*Proof. apply pow_ceil_mul_nat_divide; vm_decide. Qed.*)
  Lemma wt_divides' i : wt (S i) / wt i <> 0. Admitted.
  (*Proof. symmetry; apply Z.lt_neq, Z.gt_lt_iff, wt_divides. Qed.*)
  Definition wt_divides_chain1 i (H:In i carry_chain1) : wt (S i) / wt i <> 0 := wt_divides' i.
  Definition wt_divides_chain2 i (H:In i carry_chain2) : wt (S i) / wt i <> 0 := wt_divides' i.

  Local Ltac solve_constant_sig :=
    lazymatch goal with
    | [ |- { c : Z^?sz | Positional.Fdecode (m:=?M) ?wt c = ?v } ]
      => let t := (eval vm_compute in
                      (Positional.encode (n:=sz) (modulo:=modulo) (div:=div) wt (F.to_Z (m:=M) v))) in
         (exists t; vm_decide)
    end.

  Definition zero_sig :
    { zero : Z^sz | Positional.Fdecode (m:=m) wt zero = 0%F}.
  Proof.
    solve_constant_sig.
  Defined.

(*  Definition one_sig :
    { one : Z^sz | Positional.Fdecode (m:=m) wt one = 1%F}.
  Proof.
    solve_constant_sig.
  Defined.*)

(*  Definition a24_sig :
    { a24t : Z^sz | Positional.Fdecode (m:=m) wt a24t = F.of_Z m a24 }.
  Proof.
    solve_constant_sig.
  Defined.*)

  Require Import AdmitAxiom.

  Definition add_sig :
    { add : (Z^sz -> Z^sz -> Z^sz)%type |
               forall a b : Z^sz,
                 let eval := Positional.Fdecode (m:=m) wt in
                 eval (add a b) = (eval a  + eval b)%F }.
  Proof.
    eexists; cbv beta zeta; intros a b.
    pose proof wt_nonzero.
    let x := constr:(
        Positional.add_cps (n := sz) wt a b id) in
    F_mod_eq; presolve_op_mod_eq wt x; [ basesystem_partial_evaluation_RHS; do_replace_match_with_destructuring_match_in_goal | ].
    reflexivity.
    admit.
  Defined.

  Definition sub_sig :
    {sub : (Z^sz -> Z^sz -> Z^sz)%type |
               forall a b : Z^sz,
                 let eval := Positional.Fdecode (m:=m) wt in
                 eval (sub a b) = (eval a - eval b)%F}.
  Proof.
    eexists; cbv beta zeta; intros a b.
    pose proof wt_nonzero.
    let x := constr:(
         Positional.sub_cps (n:=sz) (coef := coef) wt a b id) in
    F_mod_eq; presolve_op_mod_eq wt x; [ basesystem_partial_evaluation_RHS; do_replace_match_with_destructuring_match_in_goal | ].
    reflexivity.
    admit.
  Defined.

  Definition opp_sig :
    {opp : (Z^sz -> Z^sz)%type |
               forall a : Z^sz,
                 let eval := Positional.Fdecode (m := m) wt in
                 eval (opp a) = F.opp (eval a)}.
  Proof.
    eexists; cbv beta zeta; intros a.
    pose proof wt_nonzero.
    let x := constr:(
         Positional.opp_cps (n:=sz) (coef := coef) wt a id) in
    F_mod_eq; presolve_op_mod_eq wt x; [ basesystem_partial_evaluation_RHS; do_replace_match_with_destructuring_match_in_goal | ].
    reflexivity.
    admit.
  Defined.

  Definition mul_sig :
    {mul : (Z^sz -> Z^sz -> Z^sz)%type |
               forall a b : Z^sz,
                 let eval := Positional.Fdecode (m := m) wt in
                 eval (mul a b) = (eval a  * eval b)%F}.
  Proof.
    eexists; cbv beta zeta; intros a b.
    pose proof wt_nonzero.
    let x := constr:(
         Positional.mul_cps (n:=sz) (m:=sz2) wt a b
                            (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)) in
    F_mod_eq; presolve_op_mod_eq wt x; [ basesystem_partial_evaluation_RHS; do_replace_match_with_destructuring_match_in_goal | ].
    reflexivity.
    admit.
  Defined.

  Definition square_sig :
    {square : (Z^sz -> Z^sz)%type |
               forall a : Z^sz,
                 let eval := Positional.Fdecode (m := m) wt in
                 eval (square a) = (eval a  * eval a)%F}.
  Proof.
    eexists; cbv beta zeta; intros a.
    pose proof wt_nonzero.
    let x := constr:(
         Positional.mul_cps (n:=sz) (m:=sz2) wt a a
                            (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)) in
    F_mod_eq; presolve_op_mod_eq wt x; [ basesystem_partial_evaluation_RHS; do_replace_match_with_destructuring_match_in_goal | ].
    reflexivity.
    admit.
  Defined.

  (* Performs a full carry loop (as specified by carry_chain) *)
  Definition carry_sig :
    {carry : (Z^sz -> Z^sz)%type |
               forall a : Z^sz,
                 let eval := Positional.Fdecode (m := m) wt in
                 eval (carry a) = eval a}.
  Proof.
    eexists; cbv beta zeta; intros a.
    pose proof wt_nonzero. pose proof wt_divides_chain1.
    pose proof div_mod. pose proof wt_divides_chain2.
    let x := constr:(
               Positional.chained_carries_cps (n:=sz) (div:=div)(modulo:=modulo) wt a carry_chain1
                  (fun r => Positional.carry_reduce_cps (n:=sz) (div:=div) (modulo:=modulo) wt s c r
                  (fun rrr => Positional.chained_carries_cps (n:=sz) (div:=div) (modulo:=modulo) wt rrr carry_chain2 id
             ))) in
    F_mod_eq; presolve_op_mod_eq wt x; [ basesystem_partial_evaluation_RHS; do_replace_match_with_destructuring_match_in_goal | ].
    reflexivity.
    admit.
  Defined.

  Section PreFreeze.
    Lemma wt_pos i : wt i > 0.
    Proof. (*eapply pow_ceil_mul_nat_pos; vm_decide. Qed.*) Admitted.

    Lemma wt_multiples i : wt (S i) mod (wt i) = 0.
    Proof. (* apply pow_ceil_mul_nat_multiples; vm_decide. Qed.*) Admitted.
  End PreFreeze.

  Hint Opaque freeze : uncps.
  Hint Rewrite freeze_id : uncps.
(*
  Definition freeze_sig :
    {freeze : (Z^sz -> Z^sz)%type |
     forall a : Z^sz,
         (0 <= Positional.eval wt a < 2 * Z.pos m)->
                 let eval := Positional.Fdecode (m := m) wt in
                 eval (freeze a) = eval a}.
  Proof.
    eexists; cbv beta zeta; intros a ?.
    pose proof wt_nonzero. pose proof wt_pos.
    pose proof div_mod. pose proof wt_divides.
    pose proof wt_multiples.
    pose proof div_correct. pose proof modulo_correct.
    let x := constr:(freeze (n:=sz) wt (Z.ones bitwidth) m_enc a) in
    F_mod_eq;
      transitivity (Positional.eval wt x); repeat autounfold;
        [ | autorewrite with uncps push_id push_basesystem_eval;
            rewrite eval_freeze with (c:=c);
            try eassumption; try omega; try reflexivity;
            try solve [auto using B.Positional.select_id,
                       B.Positional.eval_select, zselect_correct];
            vm_decide].
   cbv[mod_eq]; apply f_equal2;
     [  | reflexivity ]; apply f_equal.
   cbv - [runtime_opp runtime_add runtime_mul runtime_shr runtime_and Let_In Z.add_get_carry Z.zselect].
   reflexivity.
  Defined.
*)
(*  Definition ring :=
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
      ).
*)
(*
Eval cbv [proj1_sig add_sig] in (proj1_sig add_sig).
Eval cbv [proj1_sig sub_sig] in (proj1_sig sub_sig).
Eval cbv [proj1_sig opp_sig] in (proj1_sig opp_sig).
Eval cbv [proj1_sig mul_sig] in (proj1_sig mul_sig).
Eval cbv [proj1_sig carry_sig] in (proj1_sig carry_sig).
*)

End Ops.
