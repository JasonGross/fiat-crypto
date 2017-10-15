Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.Saturated.Freeze.
Require Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Base.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn Crypto.Util.ZUtil.Definitions.
Require Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.CacheTerm.

Module Export Exports.
  Hint Opaque freeze : uncps.
  Hint Rewrite freeze_id : uncps.
End Exports.

Local Open Scope Z_scope.
Local Infix "^" := Tuple.tuple : type_scope.

Ltac freeze_preunfold :=
  cbv [freeze freeze_cps Wrappers.Columns.unbalanced_sub_cps Wrappers.Columns.conditional_add_cps Core.Columns.from_associational_cps Core.Columns.nils Core.Columns.cons_to_nth_cps Core.Columns.compact_cps Wrappers.Columns.add_cps Core.Columns.compact_step_cps Core.Columns.compact_digit_cps].

Section gen.
  Context (m : positive)
          (sz : nat)
          (c : list limb)
          (bitwidth : Z)
          (carry_chains : list (list nat))
          (sz_nonzero : sz <> 0%nat)
          (sz_le_log2_m : Z.of_nat sz <= Z.log2_up (Z.pos m)).

  Local Notation wt := (wt_gen m sz).
  Local Notation sz2 := (sz2' sz).
  Local Notation m_enc := (m_enc' m sz).
  Local Notation wt_divides' := (wt_gen_divides' m sz sz_nonzero sz_le_log2_m).
  Local Notation wt_nonzero := (wt_gen_nonzero m sz).

  Context (c_small : 0 < Associational.eval c < wt sz)
          (m_enc_bounded : Tuple.map (BinInt.Z.land (Z.ones bitwidth)) m_enc = m_enc)
          (m_correct_wt : Z.pos m = wt sz - Associational.eval c).

  Definition freeze_sig'
    : { freeze : (Z^sz -> Z^sz)%type |
        forall a : Z^sz,
          (0 <= Positional.eval wt a < 2 * Z.pos m)->
          let eval := Positional.Fdecode (m := m) wt in
          eval (freeze a) = eval a }.
  Proof.
    eexists; cbv beta zeta; (intros a ?).
    pose proof wt_nonzero; pose proof (wt_gen_pos m sz).
    pose proof (wt_gen0_1 m sz).
    pose proof div_mod; pose proof (wt_gen_divides m sz sz_nonzero sz_le_log2_m).
    pose proof (wt_gen_multiples m sz).
    pose proof div_correct; pose proof modulo_correct.
    pose proof (wt_gen_divides_chain m sz sz_nonzero sz_le_log2_m).
    let x := constr:(freeze (n:=sz) wt (Z.ones bitwidth) m_enc a) in
    presolve_op_F constr:(wt) x; [ reflexivity | ].
    rewrite eval_freeze with (c := c);
      try (cbv [m_enc']; rewrite Positional.eval_encode by eauto);
      try eassumption; try omega; try reflexivity.

    Focus 3.

    autorewrite with push_basesystem_eval.
              try solve [auto using B.Positional.select_id,
                         B.Positional.eval_select(*, zselect_correct*)];
              vm_decide];
          cbv[mod_eq]; apply f_equal2;
          [  | reflexivity ]; apply f_equal;
          cbv - [runtime_opp runtime_add runtime_mul runtime_shr runtime_and Let_In Z.add_get_carry Z.zselect];
          reflexivity)
           freeze_sig.
  (* side condition needs cbv [Positional.mul_cps Positional.reduce_cps]. *)
  Context (mul_code_correct
           : match mul_code with
             | None => True
             | Some v
               => forall a b,
                 v a b
                 = Positional.mul_cps (n:=sz) (m:=sz2) wt a b
                                      (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)
             end)
          (square_code_correct
           : match square_code with
             | None => True
             | Some v
               => forall a,
                 v a
                 = Positional.mul_cps (n:=sz) (m:=sz2) wt a a
                                      (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)
             end).



  (* Performs a full carry loop (as specified by carry_chain) *)
  Definition carry_sig'
    : { carry : (Z^sz -> Z^sz)%type
      | forall a : Z^sz,
          let eval := Positional.Fdecode (m := m) wt in
          eval (carry a) = eval a }.
  Proof.
    let a := fresh "a" in
    eexists; cbv beta zeta; intros a.
    pose proof (wt_gen0_1 m sz).
    pose proof wt_nonzero; pose proof div_mod.
    pose proof (wt_gen_divides_chains m sz sz_nonzero sz_le_log2_m carry_chains).
    pose proof wt_divides'.
    let x := constr:(chained_carries' sz wt s c a carry_chains) in
    presolve_op_F constr:(wt) x; [ reflexivity | ].
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
  Defined.

  Definition constant_sig' v
    : { zero : Z^sz | Positional.Fdecode (m:=m) wt zero = v}.
  Proof. solve_constant_local_sig. Defined.


(* kludge to get around name clashes in the following, and the fact
     that the python script cares about argument names *)
Local Ltac rewrite_eval_freeze_with_c c' :=
  rewrite eval_freeze with (c:=c').

Ltac pose_freeze_sig sz m wt c m_enc bitwidth wt_nonzero wt_pos wt_divides wt_multiples freeze_sig :=
  cache_term_with_type_by
    {freeze : (Z^sz -> Z^sz)%type |
     forall a : Z^sz,
       (0 <= Positional.eval wt a < 2 * Z.pos m)->
       let eval := Positional.Fdecode (m := m) wt in
       eval (freeze a) = eval a}
    ltac:(let a := fresh "a" in
          eexists; cbv beta zeta; (intros a ?);
          pose proof wt_nonzero; pose proof wt_pos;
          pose proof div_mod; pose proof wt_divides;
          pose proof wt_multiples;
          pose proof div_correct; pose proof modulo_correct;
          let x := constr:(freeze (n:=sz) wt (Z.ones bitwidth) m_enc a) in
          F_mod_eq;
          transitivity (Positional.eval wt x); repeat autounfold;
          [ | autorewrite with uncps push_id push_basesystem_eval;
              rewrite_eval_freeze_with_c c;
              try eassumption; try omega; try reflexivity;
              try solve [auto using B.Positional.select_id,
                         B.Positional.eval_select(*, zselect_correct*)];
              vm_decide];
          cbv[mod_eq]; apply f_equal2;
          [  | reflexivity ]; apply f_equal;
          cbv - [runtime_opp runtime_add runtime_mul runtime_shr runtime_and Let_In Z.add_get_carry Z.zselect];
          reflexivity)
           freeze_sig.
