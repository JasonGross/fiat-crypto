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
          (m_big : Z.of_nat sz <= Z.log2_up (Z.pos m))
          (m_good : Z.pos m = s - Associational.eval c).

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
    pose proof (wt_gen_divides_chains m sz sz_nonzero m_big carry_chains).
    pose proof (wt_gen_divides' m sz sz_nonzero m_big).
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
    cbv [wt_gen QArith_base.inject_Z QArith_base.Qdiv QArith_base.Qmult QArith_base.Qnum QArith_base.Qden Qround.Qceiling QArith_base.Qopp Qround.Qfloor QArith_base.Qinv Z.of_nat].
    rewrite Pos.mul_1_l, Pos.mul_1_r.

    About nat_rect.
    repeat match goal with
           | [ |- context G[let (x, y) := match ?v with
                                          | 0 => ?a
                                          | Z.pos p => @?P p
                                          | Z.neg n => @?N n
                                          end
                            in @?Q x y] ]
             => let G' := context G[match v with
                                    | 0 => let (x, y) := a in Q x y
                                    | Z.pos p => let (x, y) := P p in Q x y
                                    | Z.neg p => let (x, y) := N p in Q x y
                                    end] in
                cut G'; [ destruct v; exact (fun k => k) | ];
                  cbv beta iota zeta
           | [ |- context G[match match ?v with O => ?Oc | S n => @?Sc n end with
                            | 0 => ?a
                            | Z.pos p => @?P p
                            | Z.neg n => @?N n
                            end] ]
             => let G' := context G[nat_rect (fun _ => _)
                                             match Oc with
                                             | 0 => a
                                             | Z.pos p => P p
                                             | Z.neg p => N p
                                             end
                                             (fun n _ => match Sc n with
                                                         | 0 => a
                                                         | Z.pos p => P p
                                                         | Z.neg p => N p
                                                         end) v] in
                cut G'; [ destruct v; exact (fun k => k) | ];
                  cbv beta iota zeta
           | [ |- context G[?f (nat_rect _ ?Oc (fun n _ => @?Sc n) ?v)] ]
             => let G' := context G[nat_rect (fun _ => _) (f Oc) (fun n _ => f (Sc n)) v] in
                cut G'; [ destruct v; exact (fun k => k) | ];
                  cbv beta iota zeta
           | [ |- context G[?f match ?v with O => ?Oc | S n => @?Sc n end] ]
             => let G' := context G[nat_rect (fun _ => _) (f Oc) (fun n _ => f (Sc n)) v] in
                cut G'; [ destruct v; exact (fun k => k) | ];
                  cbv beta iota zeta
           | [ |- context G[nat_rect
                              (fun _ => _) ?Ocf ?Scf
                              match ?v with O => ?Oc | S n => @?Sc n end] ]
             => let G' := context G[match f, v with
                                    | O, O => Ocf Oc
                                    | S n, O => Scf n Oc
                                    | O, S n => Ocf (Sc n)
                                    | S f, S v => Scf f (Sc v)
                                    end] in
                cut G'; [ destruct v; exact (fun k => k) | ];
                  cbv beta iota zeta
           | _ => progress autorewrite with zsimplify_const
           end.
    lazymatch goal with
           | [ |- context G[nat_rect
                              (fun _ => _) ?Ocf ?Scf
                              match ?v with O => ?Oc | S n => @?Sc n end] ]
               => idtac end.
           | [ |- context G[nat_rect
                       (fun _ => _) ?Ocf ?Scf
                       match ?v with O => ?Oc | S n => @?Sc n end] ]
      => idtac
    end.
             => let G' := context G[match f, v with
                                    | O, O => Ocf Oc
                                    | S n, O => Scf n Oc
                                    | O, S n => Ocf (Sc n)
                                    | S f, S v => Scf f (Sc v)
                                    end] in
                cut G'; [ destruct v; exact (fun k => k) | ];
                  cbv beta iota zeta

    end.
    .| [ |- context G[?f match ?v with O => ?Oc | S n => @?Sc n end] ]
      => let G' := context G[nat_rect (fun _ => _) (f Oc) (fun n _ => f (Sc n)) v] in
         cut G'; [ destruct v; exact (fun k => k) | ];
           cbv beta iota zeta
    end.
    | [ |- context G[match ?f with O => ?Ocf | S n => @?Scf n end
                       match ?v with O => ?Oc | S n => @?Sc n end] ]
      => idtac end.
      => let G' := context G[match f, v with
                                    | O, O => Ocf Oc
                                    | S n, O => Scf n Oc
                                    | O, S n => Ocf (Sc n)
                                    | S f, S v => Scf f (Sc v)
                                    end] in
                cut G'; [ destruct v; exact (fun k => k) | ];
                  cbv beta iota zeta
    end.
    .

          basesystem_partial_evaluation_RHS.
          do_replace_match_with_destructuring_match_in_goal.

    Locate Ltac solve_op_mod_eq.
    Print Ltac solve_op_F.
    solve_op_F (wt_gen m sz) x.
    pose x.
    let x := make_chained_carries_cps sz wt s c a carry_chains in
    pose x.
          solve_op_F wt x; reflexivity)
           carry_sig.

(* Performs a full carry loop (as specified by carry_chain) *)
Ltac pose_carry_sig sz m wt s c carry_chains wt_nonzero wt_divides_chains carry_sig :=
  cache_term_with_type_by
    {carry : (Z^sz -> Z^sz)%type |
     forall a : Z^sz,
       let eval := Positional.Fdecode (m := m) wt in
       eval (carry a) = eval a}
    ltac:(idtac;
          let a := fresh "a" in
          eexists; cbv beta zeta; intros a;
          pose proof wt_nonzero; pose proof div_mod;
          pose_proof_tuple wt_divides_chains;
          let x := make_chained_carries_cps sz wt s c a carry_chains in
          solve_op_F wt x; reflexivity)
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
