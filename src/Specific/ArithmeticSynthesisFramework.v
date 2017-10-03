Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Arithmetic.Saturated.Freeze.
Require Crypto.Specific.CurveParameters.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.TransparentAssert.
Require Crypto.Util.Tuple.
Require Import Crypto.Util.QUtil.
Require Import Crypto.Util.ZRange Crypto.Util.BoundedWord.
Require Import Crypto.Util.FixedWordSizes.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.CacheTerm.
Local Notation tuple := Tuple.tuple.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Coercion Z.of_nat : nat >-> Z.

Section wt.
  Import QArith Qround.
  Local Coercion QArith_base.inject_Z : Z >-> Q.
  Definition wt_gen (m : positive) (sz : nat) (i:nat) : Z := 2^Qceiling((Z.log2_up m/sz)*i).
End wt.

Module Export Package.
  Local Infix "^" := tuple : type_scope.

  Class ArithmeticSynthesisTestParams :=
    {
      m : positive;
      sz : nat;
      a24 : Z;
      lgbitwidth : nat;
      adjusted_bitwidth : nat;
      bounds : Tuple.tuple zrange sz;
      allowable_bit_widths : list nat;
      freeze_allowable_bit_widths : list nat;
    }.

  Class ArithmeticSynthesisTestPackage' {TP : ArithmeticSynthesisTestParams} :=
    {
      wt : nat -> Z
      := wt_gen m sz;

      a24_sig
      : { a24t : Z ^ sz
        | Positional.Fdecode wt a24t = F.of_Z m a24 };
      add_sig
      : { add : Z ^ sz -> Z ^ sz -> Z ^ sz
        | forall a b : Z ^ sz,
            let eval := Positional.Fdecode (m:=m) wt in
            eval (add a b) = (eval a + eval b)%F };
      sub_sig
      : { sub : Z ^ sz -> Z ^ sz -> Z ^ sz
        | forall a b : Z ^ sz,
            let eval := Positional.Fdecode (m:=m) wt in
            eval (sub a b) = (eval a - eval b)%F };
      opp_sig
      : { opp : Z ^ sz -> Z ^ sz
        | forall a : Z ^ sz,
            let eval := Positional.Fdecode (m:=m) wt in
            eval (opp a) = F.opp (eval a) };
      mul_sig
      : { mul : Z ^ sz -> Z ^ sz -> Z ^ sz
        | forall a b : Z ^ sz,
            let eval := Positional.Fdecode (m:=m) wt in
            eval (mul a b) = (eval a * eval b)%F };
      square_sig
      : { square : Z ^ sz -> Z ^ sz
        | forall a : Z ^ sz,
            let eval := Positional.Fdecode (m:=m) wt in
            eval (square a) = (eval a * eval a)%F };
      carry_sig
      : { carry : Z ^ sz -> Z ^ sz
        | forall a : Z ^ sz,
            let eval := Positional.Fdecode (m:=m) wt in
            eval (carry a) = eval a };
      freeze_sig
      : { freeze : Z ^ sz -> Z ^ sz
        | forall a : Z ^ sz,
            (0 <= Positional.eval wt a < 2 * Z.pos m)->
            let eval := Positional.Fdecode (m:=m) wt in
            eval (freeze a) = eval a };

      feW
      := Tuple.tuple (wordT lgbitwidth) sz;
      feBW
      := BoundedWord sz adjusted_bitwidth bounds;

      phiW : feW -> F m
      := fun x => B.Positional.Fdecode wt (Tuple.map wordToZ x);
      phiBW : feBW -> F m
      := fun x => B.Positional.Fdecode wt (BoundedWordToZ _ _ _ x);

      feW_bounded : feW -> Prop;

      feBW_to_Z : feBW -> tuple Z sz;
      feBW_bounded : forall (a : feBW),
          0 <= B.Positional.eval wt (feBW_to_Z a) < 2 * Z.pos m;
    }.

  Class > ArithmeticSynthesisTestPackage
    := { ASParams :> ArithmeticSynthesisTestParams;
         ASPackage :> @ArithmeticSynthesisTestPackage' ASParams }.
  Coercion ASPackage : ArithmeticSynthesisTestPackage >-> ArithmeticSynthesisTestPackage'.
  Coercion ASParams : ArithmeticSynthesisTestPackage >-> ArithmeticSynthesisTestParams.
  Coercion Build_ArithmeticSynthesisTestPackage : ArithmeticSynthesisTestPackage' >-> ArithmeticSynthesisTestPackage.

  Declare Reduction package_red
    := cbv [id
              ASParams
              ASPackage
              m
              sz
              a24
              wt
              a24_sig
              add_sig
              sub_sig
              opp_sig
              mul_sig
              square_sig
              carry_sig
              freeze_sig
              lgbitwidth
              adjusted_bitwidth
              bounds
              feW
              feBW
              phiW
              phiBW
              feW_bounded
              feBW_to_Z
              feBW_bounded
              allowable_bit_widths
              freeze_allowable_bit_widths].
End Package.

Module Synthesize (Curve : CurveParameters.CurveParameters).
  Hint Opaque freeze : uncps.
  Hint Rewrite freeze_id : uncps.

  Module Import Internal.
    Module P := CurveParameters.FillCurveParameters Curve.

    Local Infix "^" := tuple : type_scope.

    Ltac pose_get_ident term id :=
      cache_term term id.
    Ltac assert_get_ident id ty pre_tac tac :=
      cache_term_with_type_by_gen ty ltac:(fun id' => pre_tac; abstract tac using id') id.
    Ltac transparent_assert_get_ident id ty pre_tac tac :=
      cache_term_with_type_by_gen ty ltac:(fun id' => pre_tac; transparent_abstract tac using id') id.

    (* These definitions will need to be passed as Ltac arguments (or
     cleverly inferred) when things are eventually automated *)
    Ltac pose_computed Pv v :=
      let v' := P.do_compute Pv in
      pose_get_ident v' v.
    Ltac pose_unfolded Pv v :=
      let v' := P.do_unfold Pv in
      pose_get_ident v' v.
    Ltac pose_sz sz := pose_computed P.sz sz.
    Ltac pose_bitwidth bitwidth := pose_computed P.bitwidth bitwidth.
    Ltac pose_s s := pose_unfolded P.s s. (* don't want to compute, e.g., [2^255] *)
    Ltac pose_c c := pose_computed P.c c.
    Ltac pose_carry_chain1 carry_chain1 := pose_computed P.carry_chain1 carry_chain1.
    Ltac pose_carry_chain2 carry_chain2 := pose_computed P.carry_chain2 carry_chain2.

    Ltac pose_a24 a24 := pose_computed P.a24 a24.

    Ltac pose_coef_div_modulus coef_div_modulus :=
      pose_computed P.coef_div_modulus coef_div_modulus.

    (* These definitions are inferred from those above *)
    Ltac pose_m s c m :=  (* modulus *)
      let m' := (eval vm_compute in (Z.to_pos (s - Associational.eval c))) in
      pose_get_ident m' m.

    Ltac pose_wt m sz wt :=
      let wt' := (eval cbv [wt_gen] in (wt_gen m sz)) in
      pose_get_ident wt' wt.
    Ltac pose_sz2 sz sz2 :=
      let sz2' := (eval vm_compute in ((sz * 2) - 1)%nat) in
      pose_get_ident sz2' sz2.
    Ltac pose_m_enc sz wt s c m_enc :=
      let m_enc' := (eval vm_compute in (Positional.encode (modulo:=modulo) (div:=div) (n:=sz) wt (s-Associational.eval c))) in
      let m_enc' := (eval cbv in m_enc') in (* compute type arguments *)
      pose_get_ident m_enc' m_enc.
    Ltac pose_coef sz wt m_enc coef_div_modulus coef := (* subtraction coefficient *)
      let coef' := (eval vm_compute in
                       ((fix addm (acc: Z^sz) (ctr : nat) : Z^sz :=
                           match ctr with
                           | O => acc
                           | S n => addm (Positional.add_cps wt acc m_enc id) n
                           end) (Positional.zeros sz) coef_div_modulus)) in
      let coef' := (eval cbv in coef') in (* compute type arguments *)
      pose_get_ident coef' coef.
    Ltac pose_coef_mod m sz wt coef coef_mod :=
      pose_get_ident (eq_refl : mod_eq m (Positional.eval (n:=sz) wt coef) 0) coef_mod.
    Ltac pose_sz_nonzero sz sz_nonzero :=
      assert_get_ident sz_nonzero (sz <> 0%nat) ltac:(clear) ltac:(idtac; vm_decide_no_check).
    Ltac pose_wt_nonzero wt wt_nonzero :=
      assert_get_ident
        wt_nonzero (forall i, wt i <> 0)
        ltac:(clear) ltac:(eapply pow_ceil_mul_nat_nonzero; vm_decide_no_check).
    Ltac pose_wt_divides wt wt_divides :=
      assert_get_ident
        wt_divides (forall i, wt (S i) / wt i > 0)
        ltac:(clear) ltac:(apply pow_ceil_mul_nat_divide; vm_decide_no_check).
    Ltac pose_wt_divides' wt wt_divides wt_divides' :=
      assert_get_ident
        wt_divides' (forall i, wt (S i) / wt i <> 0)
        ltac:(clear) ltac:(symmetry; apply Z.lt_neq, Z.gt_lt_iff, wt_divides).
    Ltac pose_wt_divides_chain carry_chain wt wt_divides' wt_divides_chain :=
      assert_get_ident
        wt_divides_chain (forall i (H:In i carry_chain), wt (S i) / wt i <> 0)
        ltac:(clear) ltac:(let i := fresh "i" in intros i ?; exact (wt_divides' i)).

    Local Ltac solve_constant_sig sz wt :=
      idtac;
      lazymatch goal with
      | [ |- { c : Z^?sz | Positional.Fdecode (m:=?M) ?wt c = ?v } ]
        => let t := (eval vm_compute in
                        (Positional.encode (n:=sz) (modulo:=modulo) (div:=div) wt (F.to_Z (m:=M) v))) in
           (exists t; clear; vm_decide)
      end.

    Ltac pose_zero_sig m sz wt zero_sig :=
      transparent_assert_get_ident
        zero_sig { zero : Z^sz | Positional.Fdecode (m:=m) wt zero = 0%F}
        ltac:(clear) ltac:(solve_constant_sig sz wt).

    Ltac pose_one_sig m sz wt one_sig :=
      transparent_assert_get_ident
        one_sig { one : Z^sz | Positional.Fdecode (m:=m) wt one = 1%F}
        ltac:(clear) ltac:(solve_constant_sig sz wt).

    Ltac pose_a24_sig m sz wt a24 a24_sig :=
      transparent_assert_get_ident
        a24_sig { a24t : Z^sz | Positional.Fdecode (m:=m) wt a24t = F.of_Z m a24 }
        ltac:(clear) ltac:(solve_constant_sig sz wt).

    Ltac abstract_sig tac :=
      idtac;
      lazymatch goal with
      | [ |- sig ?P ]
        => let H := fresh in
           transparent assert (H : (sig P)) by (tac ());
           let Hv := (eval cbv delta [H] in H) in
           clear -H; clear H;
           let p1 := (eval cbv [proj1_sig] in (proj1_sig Hv)) in
           (exists p1);
           abstract exact (proj2_sig Hv)
      end.

    Ltac pose_add_sig m sz wt wt_nonzero add_sig :=
      transparent_assert_get_ident
        add_sig
        { add : (Z^sz -> Z^sz -> Z^sz)%type |
          forall a b : Z^sz,
            let eval := Positional.Fdecode (m:=m) wt in
            eval (add a b) = (eval a + eval b)%F }
        ltac:(idtac)
        ltac:(abstract_sig
                ltac:(fun _ =>
                        let a := fresh "a" in
                        let b := fresh "b" in
                        eexists; cbv beta zeta; intros a b;
                        generalize wt_nonzero; clear; intro;
                        let x := constr:(
                                   Positional.add_cps (n := sz) wt a b id) in
                        solve_op_F wt x;
                        reflexivity
                     )).

    Ltac pose_sub_sig m sz wt wt_nonzero coef sub_sig :=
      transparent_assert_get_ident
        sub_sig
        {sub : (Z^sz -> Z^sz -> Z^sz)%type |
         forall a b : Z^sz,
           let eval := Positional.Fdecode (m:=m) wt in
           eval (sub a b) = (eval a - eval b)%F}
        ltac:(idtac)
        ltac:(abstract_sig
                ltac:(fun _ =>
                        let a := fresh "a" in
                        let b := fresh "b" in
                        eexists; cbv beta zeta; intros a b;
                        generalize wt_nonzero; clear (*-coef*); intro;
                        let x := constr:(
                                   Positional.sub_cps (n:=sz) (coef := coef) wt a b id) in
                        solve_op_F wt x;
                        reflexivity
                     )).

    Ltac pose_opp_sig m sz wt wt_nonzero coef opp_sig :=
      transparent_assert_get_ident
        opp_sig
        {opp : (Z^sz -> Z^sz)%type |
         forall a : Z^sz,
           let eval := Positional.Fdecode (m := m) wt in
           eval (opp a) = F.opp (eval a)}
        ltac:(idtac)
        ltac:(abstract_sig
                ltac:(fun _ =>
                        let a := fresh "a" in
                        eexists; cbv beta zeta; intros a;
                        generalize wt_nonzero; clear (*-coef*); intro;
                        let x := constr:(
                                   Positional.opp_cps (n:=sz) (coef := coef) wt a id) in
                        solve_op_F wt x;
                        reflexivity
                     )).

    Ltac pose_mul_sig m sz wt wt_nonzero sz2 s c mul_sig :=
      transparent_assert_get_ident
        mul_sig
        {mul : (Z^sz -> Z^sz -> Z^sz)%type |
         forall a b : Z^sz,
           let eval := Positional.Fdecode (m := m) wt in
           eval (mul a b) = (eval a * eval b)%F}
        ltac:(idtac)
        ltac:(abstract_sig
                ltac:(fun _ =>
                        let a := fresh "a" in
                        let b := fresh "b" in
                        eexists; cbv beta zeta; intros a b;
                        generalize wt_nonzero; clear (*-sz2 s c*); intro;
                        let x := constr:(
                                   Positional.mul_cps (n:=sz) (m:=sz2) wt a b
                                                      (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)) in
                        solve_op_F wt x;
                        P.default_mul;
                        P.extra_prove_mul_eq;
                        break_match; cbv [Let_In runtime_mul runtime_add]; repeat apply (f_equal2 pair); rewrite ?Z.shiftl_mul_pow2 by omega; ring
                     )).

    Ltac pose_square_sig m sz wt wt_nonzero sz2 s c square_sig :=
      transparent_assert_get_ident
        square_sig
        {square : (Z^sz -> Z^sz)%type |
         forall a : Z^sz,
           let eval := Positional.Fdecode (m := m) wt in
           eval (square a) = (eval a * eval a)%F}
        ltac:(idtac)
        ltac:(abstract_sig
                ltac:(fun _ =>
                        let a := fresh "a" in
                        eexists; cbv beta zeta; intros a;
                        generalize wt_nonzero; clear (*-sz2 s c*); intro;
                        let x := constr:(
                                   Positional.mul_cps (n:=sz) (m:=sz2) wt a a
                                                      (fun ab => Positional.reduce_cps (n:=sz) (m:=sz2) wt s c ab id)) in
                        solve_op_F wt x;
                        P.default_square;
                        P.extra_prove_square_eq;
                        break_match; cbv [Let_In runtime_mul runtime_add]; repeat apply (f_equal2 pair); rewrite ?Z.shiftl_mul_pow2 by omega; ring
                     )).

    (* Performs a full carry loop (as specified by carry_chain) *)
    Ltac pose_carry_sig m sz wt wt_nonzero wt_divides_chain1 wt_divides_chain2 carry_chain1 carry_chain2 s c carry_sig :=
      transparent_assert_get_ident
        carry_sig
        {carry : (Z^sz -> Z^sz)%type |
         forall a : Z^sz,
           let eval := Positional.Fdecode (m := m) wt in
           eval (carry a) = eval a}
        ltac:(idtac)
        ltac:(abstract_sig
                ltac:(fun _ =>
                        let a := fresh "a" in
                        eexists; cbv beta zeta; intros a;
                        generalize wt_divides_chain2; generalize div_mod;
                        generalize wt_divides_chain1; generalize wt_nonzero;
                        clear (*-carry_chain1 carry_chain2 s c*); (intros ????);
                        let x := constr:(
                                   Positional.chained_carries_cps (n:=sz) (div:=div)(modulo:=modulo) wt a carry_chain1
                                                                  (fun r => Positional.carry_reduce_cps (n:=sz) (div:=div) (modulo:=modulo) wt s c r
                                                                                                        (fun rrr => Positional.chained_carries_cps (n:=sz) (div:=div) (modulo:=modulo) wt rrr carry_chain2 id
                                 ))) in
                        solve_op_F wt x;
                        reflexivity
                     )).

    Ltac pose_wt_pos wt wt_pos :=
      assert_get_ident
        wt_pos (forall i, wt i > 0)
        ltac:(clear) ltac:(eapply pow_ceil_mul_nat_pos; vm_decide_no_check).

    Ltac pose_wt_multiples wt wt_multiples :=
      assert_get_ident
        wt_multiples (forall i, wt (S i) mod (wt i) = 0)
        ltac:(clear) ltac:(apply pow_ceil_mul_nat_multiples; vm_decide_no_check).

    Ltac pose_freeze_sig m sz wt wt_nonzero wt_pos wt_divides wt_multiples bitwidth m_enc c' freeze_sig :=
      transparent_assert_get_ident
        freeze_sig
        {freeze : (Z^sz -> Z^sz)%type |
         forall a : Z^sz,
           (0 <= Positional.eval wt a < 2 * Z.pos m)->
           let eval := Positional.Fdecode (m := m) wt in
           eval (freeze a) = eval a}
        ltac:(idtac)
        ltac:(abstract_sig
                ltac:(fun _ =>
                        let a := fresh "a" in
                        let H := fresh "H" in
                        eexists; cbv beta zeta; (intros a H);
                        generalize modulo_correct; generalize div_correct;
                        generalize wt_multiples;
                        generalize wt_divides; generalize div_mod;
                        generalize wt_pos; generalize wt_nonzero;
                        clear -(*bitwidth m_enc c'*) H; (intros ???????);
                        let x := constr:(freeze (n:=sz) wt (Z.ones bitwidth) m_enc a) in
                        F_mod_eq;
                        transitivity (Positional.eval wt x); repeat autounfold;
                        [ | autorewrite with uncps push_id push_basesystem_eval;
                            rewrite eval_freeze with (c:=c');
                            try eassumption; try omega; try reflexivity;
                            try solve [auto using B.Positional.select_id,
                                       B.Positional.eval_select, Zselect.Z.zselect_correct];
                            vm_decide];
                        cbv[mod_eq]; apply f_equal2;
                        [  | reflexivity ]; apply f_equal;
                        cbv - [runtime_opp runtime_add runtime_mul runtime_shr runtime_and Let_In Z.add_get_carry Z.zselect];
                        reflexivity
                     )).

    Ltac pose_ring m sz wt zero_sig one_sig opp_sig add_sig sub_sig mul_sig sz_nonzero' wt wt_nonzero wt_divides' ring :=
      pose_get_ident
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
              (sz_nonzero := sz_nonzero')
              (div_mod := div_mod)
              wt eq_refl wt_nonzero wt_divides')
           (Positional.eq_Feq_iff wt)
           (proj2_sig add_sig)
           (proj2_sig sub_sig)
           (proj2_sig mul_sig)
        )
        ring.

    Local Notation b_of exp := {| lower := 0 ; upper := P.upper_bound_of_exponent exp |}%Z (only parsing). (* max is [(0, 2^(exp+2) + 2^exp + 2^(exp-1) + 2^(exp-3) + 2^(exp-4) + 2^(exp-5) + 2^(exp-6) + 2^(exp-10) + 2^(exp-12) + 2^(exp-13) + 2^(exp-14) + 2^(exp-15) + 2^(exp-17) + 2^(exp-23) + 2^(exp-24))%Z] *)
    (* The definition [bounds_exp] is a tuple-version of the
     limb-widths, which are the [exp] argument in [b_of] above, i.e.,
     the approximate base-2 exponent of the bounds on the limb in that
     position. *)

    Ltac pose_limb_widths wt sz limb_widths :=
      let limb_widths' := (eval vm_compute in (List.map (fun i => Z.log2 (wt (S i) / wt i)) (seq 0 sz))) in
      pose_get_ident limb_widths' limb_widths.

    Ltac pose_bounds_exp sz limb_widths bounds_exp :=
      let bounds_exp' := (eval compute in
                             (Tuple.from_list sz limb_widths eq_refl)) in
      pose_get_ident (bounds_exp' : Tuple.tuple Z sz) bounds_exp.

    Ltac pose_bounds sz bounds_exp bounds :=
      let bounds' := (eval compute in
                         (Tuple.map (fun e => b_of e) bounds_exp)) in
      pose_get_ident (bounds' : Tuple.tuple zrange sz) bounds.

    Ltac pose_lgbitwidth limb_widths lgbitwidth :=
      let lgbitwidth' := (eval compute in (Z.to_nat (Z.log2_up (List.fold_right Z.max 0 limb_widths)))) in
      pose_get_ident lgbitwidth' lgbitwidth.
    Ltac pose_adjusted_bitwidth lgbitwidth adjusted_bitwidth :=
      let adjusted_bitwidth' := (eval compute in (2^lgbitwidth)%nat) in
      pose_get_ident adjusted_bitwidth' adjusted_bitwidth.

    Ltac pose_feZ sz feZ :=
      pose_get_ident (tuple Z sz) feZ.
    Ltac pose_feW sz lgbitwidth feW :=
      let feW' := (eval cbv [lgbitwidth] in (tuple (wordT lgbitwidth) sz)) in
      pose_get_ident feW' feW.
    Ltac pose_feW_bounded bounds feW feW_bounded :=
      let feW_bounded' := (eval cbv [bounds] in (fun w : feW => is_bounded_by None bounds (Tuple.map wordToZ w))) in
      pose_get_ident feW_bounded' feW_bounded.
    Ltac pose_feBW adjusted_bitwidth bounds sz feBW :=
      let feBW' := (eval cbv [adjusted_bitwidth bounds] in (BoundedWord sz adjusted_bitwidth bounds)) in
      pose_get_ident feBW' feBW.

    Ltac pose_phiBW m wt feBW phiBW :=
      pose_get_ident
        (fun x : feBW => (B.Positional.Fdecode wt (BoundedWordToZ _ _ _ x) : F m))
        phiBW.

    Ltac pose_phiW m wt feW phiW :=
      pose_get_ident
        (fun x : feW => (B.Positional.Fdecode wt (Tuple.map wordToZ x) : F m))
        phiW.

    Ltac pose_feBW_bounded m sz wt adjusted_bitwidth bounds feBW feBW_bounded :=
      assert_get_ident
        feBW_bounded
        (forall (a : feBW),
            0 <= B.Positional.eval wt (BoundedWordToZ sz adjusted_bitwidth bounds a) < 2 * Z.pos m)
        ltac:(clear)
        ltac:(let a := fresh "a" in
              let H := fresh "H" in
              intros a;
              destruct a as [a H]; unfold BoundedWordToZ, proj1_sig;
              revert H;
              cbv -[Z.le Z.add Z.mul Z.lt fst snd wordToZ wt]; cbn [fst snd];
              repeat match goal with
                     | [ |- context[wt ?n] ]
                       => let v := (eval compute in (wt n)) in change (wt n) with v
                     end;
              intro; destruct_head'_and;
              omega
             ).

    Ltac pose_allowable_bit_widths allowable_bit_widths :=
      pose_computed P.allowable_bit_widths allowable_bit_widths.
    Ltac pose_freeze_allowable_bit_widths freeze_allowable_bit_widths :=
      pose_computed P.freeze_allowable_bit_widths freeze_allowable_bit_widths.
  End Internal.

  Ltac synthesize _ :=
    let sz := fresh "sz" in
    let bitwidth := fresh "bitwidth" in
    let s := fresh "s" in
    let c := fresh "c" in
    let carry_chain1 := fresh "carry_chain1" in
    let carry_chain2 := fresh "carry_chain2" in
    let a24 := fresh "a24" in
    let coef_div_modulus := fresh "coef_div_modulus" in
    let m := fresh "m" in
    let wt := fresh "wt" in
    let sz2 := fresh "sz2" in
    let m_enc := fresh "m_enc" in
    let coef := fresh "coef" in
    let coef_mod := fresh "coef_mod" in
    let sz_nonzero := fresh "sz_nonzero" in
    let wt_nonzero := fresh "wt_nonzero" in
    let wt_divides := fresh "wt_divides" in
    let wt_divides' := fresh "wt_divides'" in
    let wt_divides_chain1 := fresh "wt_divides_chain1" in
    let wt_divides_chain2 := fresh "wt_divides_chain2" in
    let zero_sig := fresh "zero_sig" in
    let one_sig := fresh "one_sig" in
    let a24_sig := fresh "a24_sig" in
    let add_sig := fresh "add_sig" in
    let sub_sig := fresh "sub_sig" in
    let opp_sig := fresh "opp_sig" in
    let mul_sig := fresh "mul_sig" in
    let square_sig := fresh "square_sig" in
    let carry_sig := fresh "carry_sig" in
    let wt_pos := fresh "wt_pos" in
    let wt_multiples := fresh "wt_multiples" in
    let freeze_sig := fresh "freeze_sig" in
    let ring := fresh "ring" in
    let limb_widths := fresh "limb_widths" in
    let bounds_exp := fresh "bounds_exp" in
    let bounds := fresh "bounds" in
    let lgbitwidth := fresh "lgbitwidth" in
    let adjusted_bitwidth := fresh "adjusted_bitwidth" in
    let feZ := fresh "feZ" in
    let feW := fresh "feW" in
    let feW_bounded := fresh "feW_bounded" in
    let feBW := fresh "feBW" in
    let feBW_bounded := fresh "feBW_bounded" in
    let phiBW := fresh "phiBW" in
    let phiW := fresh "phiW" in
    let allowable_bit_widths := fresh "allowable_bit_widths" in
    let freeze_allowable_bit_widths := fresh "freeze_allowable_bit_widths" in
    let sz := pose_sz sz in
    let bitwidth := pose_bitwidth bitwidth in
    let s := pose_s s in
    let c := pose_c c in
    let carry_chain1 := pose_carry_chain1 carry_chain1 in
    let carry_chain2 := pose_carry_chain2 carry_chain2 in
    let a24 := pose_a24 a24 in
    let coef_div_modulus := pose_coef_div_modulus coef_div_modulus in
    let m := pose_m s c m in
    let wt := pose_wt m sz wt in
    let sz2 := pose_sz2 sz sz2 in
    let m_enc := pose_m_enc sz wt s c m_enc in
    let coef := pose_coef sz wt m_enc coef_div_modulus coef in
    let coef_mod := pose_coef_mod m sz wt coef coef_mod in
    let sz_nonzero := pose_sz_nonzero sz sz_nonzero in
    let wt_nonzero := pose_wt_nonzero wt wt_nonzero in
    let wt_divides := pose_wt_divides wt wt_divides in
    let wt_divides' := pose_wt_divides' wt wt_divides wt_divides' in
    let wt_divides_chain1 := pose_wt_divides_chain carry_chain1 wt wt_divides' wt_divides_chain1 in
    let wt_divides_chain2 := pose_wt_divides_chain carry_chain2 wt wt_divides' wt_divides_chain2 in
    let zero_sig := pose_zero_sig m sz wt zero_sig in
    let one_sig := pose_one_sig m sz wt one_sig in
    let a24_sig := pose_a24_sig m sz wt a24 a24_sig in
    let add_sig := pose_add_sig m sz wt wt_nonzero add_sig in
    let sub_sig := pose_sub_sig m sz wt wt_nonzero coef sub_sig in
    let opp_sig := pose_opp_sig m sz wt wt_nonzero coef opp_sig in
    let mul_sig := pose_mul_sig m sz wt wt_nonzero sz2 s c mul_sig in
    let square_sig := pose_square_sig m sz wt wt_nonzero sz2 s c square_sig in
    let carry_sig := pose_carry_sig m sz wt wt_nonzero wt_divides_chain1 wt_divides_chain2 carry_chain1 carry_chain2 s c carry_sig in
    let wt_pos := pose_wt_pos wt wt_pos in
    let wt_multiples := pose_wt_multiples wt wt_multiples in
    let freeze_sig := pose_freeze_sig m sz wt wt_nonzero wt_pos wt_divides wt_multiples bitwidth m_enc c freeze_sig in
    let ring := pose_ring m sz wt zero_sig one_sig opp_sig add_sig sub_sig mul_sig sz_nonzero wt wt_nonzero wt_divides' ring in
    let limb_widths := pose_limb_widths wt sz limb_widths in
    let bounds_exp := pose_bounds_exp sz limb_widths bounds_exp in
    let bounds := pose_bounds sz bounds_exp bounds in
    let lgbitwidth := pose_lgbitwidth limb_widths lgbitwidth in
    let adjusted_bitwidth := pose_adjusted_bitwidth lgbitwidth adjusted_bitwidth in
    let feZ := pose_feZ sz feZ in
    let feW := pose_feW sz lgbitwidth feW in
    let feW_bounded := pose_feW_bounded bounds feW feW_bounded in
    let feBW := pose_feBW adjusted_bitwidth bounds sz feBW in
    let feBW_bounded := pose_feBW_bounded m sz wt adjusted_bitwidth bounds feBW feBW_bounded in
    let phiBW := pose_phiBW m wt feBW phiBW in
    let phiW := pose_phiW m wt feW phiW in
    let allowable_bit_widths := pose_allowable_bit_widths allowable_bit_widths in
    let freeze_allowable_bit_widths := pose_freeze_allowable_bit_widths freeze_allowable_bit_widths in
    let do_refine_package _ :=
        simple refine {|
                 ASPackage :=
                   (@Build_ArithmeticSynthesisTestPackage'
                      ({|
                          m := m;
                          sz := sz;
                          a24 := a24;
                          lgbitwidth := lgbitwidth;
                          adjusted_bitwidth := adjusted_bitwidth;
                          bounds := bounds;
                          allowable_bit_widths := allowable_bit_widths;
                          freeze_allowable_bit_widths := freeze_allowable_bit_widths;
                        |})
                      a24_sig
                      add_sig
                      sub_sig
                      opp_sig
                      mul_sig
                      square_sig
                      carry_sig
                      freeze_sig
                      feW_bounded
                      (BoundedWordToZ sz adjusted_bitwidth bounds)
                      feBW_bounded)
               |} in
    lazymatch goal with
    | [ |- ArithmeticSynthesisTestPackage ]
      => do_refine_package ()
    | [ |- ?e ]
      => tryif is_evar e then do_refine_package () else idtac
    | _ => idtac
    end.
End Synthesize.

(*
Eval cbv [proj1_sig add_sig] in (proj1_sig add_sig).
Eval cbv [proj1_sig sub_sig] in (proj1_sig sub_sig).
Eval cbv [proj1_sig opp_sig] in (proj1_sig opp_sig).
Eval cbv [proj1_sig mul_sig] in (proj1_sig mul_sig).
Eval cbv [proj1_sig carry_sig] in (proj1_sig carry_sig).
*)

(* Require Import Crypto.Specific.X25519.C64.CurveParameters.

Module S := Synthesize Curve.

Definition synthesized' : ArithmeticSynthesisTestPackage.
Proof. Time S.synthesize (). Time Defined.

Time Definition synthesized :=
  Eval cbv zeta delta [synthesized'] in synthesized'.
*)
