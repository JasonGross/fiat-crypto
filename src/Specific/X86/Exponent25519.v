Require Import Coq.ZArith.ZArith Coq.micromega.Psatz.
Require Import Crypto.Spec.Ed25519.
Require Import Crypto.Specific.X86.Core.
Require Import Crypto.EdDSARepChange.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.X86ToZLike.
Require Import Crypto.BoundedArithmetic.X86ToZLikeProofs.
Require Import Crypto.BoundedArithmetic.Eta.
Require Import Crypto.ModularArithmetic.BarrettReduction.ZBounded.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.LetIn.
Import NPeano.

Local Notation modulusv := (2^252 + 27742317777372353535851937790883648493)%Z.
Local Coercion Z.of_nat : nat >-> Z.
Local Notation eta x := (fst x, snd x).
Local Notation eta3 x := (eta (fst x), snd x).
Local Notation eta4 x := (eta3 (fst x), snd x).
Local Notation eta4' x := (eta (fst x), eta (snd x)).

Section x86.
  Local Notation base := 2%Z (* TODO(@andres-erbsen): Is this the correct base, or are we using something else? *).
  Local Notation smaller_bound_exp := 250%Z (* TODO(@andres-erbsen): Is this the correct smaller size (2^250), or are we using something else? *).
  Lemma smaller_bound_smaller : (0 <= smaller_bound_exp <= 256)%Z. Proof. vm_compute; intuition congruence. Qed.
  Lemma modulusv_in_range : 0 <= modulusv < 2 ^ 256. Proof. vm_compute; intuition congruence. Qed.
  Lemma modulusv_pos : 0 < modulusv. Proof. vm_compute; reflexivity. Qed.
  Section gen_modulus.
    Context (modulus : Z)
            (modulus_in_range : 0 <= modulus < 2 ^ 256)
            (modulus_pos : 0 < modulus).
    Section gen.
      Context (half_n : nat).
      Local Notation n := (2 * half_n)%nat.
      Context (ops : x86.instructions n) (props : x86.arithmetic ops)
              (n_pos : (0 < n)%Z)
              (n_pow_2 : (2^Nat.log2 (256 / n) = 256)%Z).
      Let ops' ldi_modulus ldi_0 : ZBounded.ZLikeOps (2^256) (2^smaller_bound_exp) modulus
        := (@ZLikeOps_of_x86_gen_Factored 256 n ops modulus smaller_bound_exp ldi_modulus ldi_0).
      Local Existing Instance ops'.
      Lemma full_width_pos : (0 < 256)%Z. Proof. omega. Qed.
      Let props' ldi_modulus ldi_0 Hldi_modulus Hldi_0 : ZBounded.ZLikeProperties (ops' ldi_modulus ldi_0)
        := @ZLikeProperties_of_x86_gen_Factored half_n 256 ops modulus props ldi_modulus ldi_0 Hldi_modulus Hldi_0 modulus_in_range smaller_bound_exp smaller_bound_smaller n_pos full_width_pos.
      Local Existing Instance props'.

      Let offset'0 := Eval compute in ((256 - smaller_bound_exp) / 2)%Z.
      Let k'0 := Eval compute in ((256 - offset'0) / Z.log2 base)%Z.
      Section params_gen.
        Import BarrettBundled.
        Context (ldi_modulus ldi_0 ldi_μ0 : Core.repeated_tuple x86.W 2 (Nat.log2 (256 / n))).
        Let offset' := Eval compute in offset'0.
        Let k' := Eval compute in k'0.
        Local Instance x86_25519_Barrett : BarrettParameters
          := { m := modulus;
               b := base;
               k := k';
               offset := offset';
               ops := ops' ldi_modulus ldi_0;
               μ' := ldi_μ0 }.
        Local Instance x86_25519_BarrettProofs
              Hldi_modulus Hldi_0
              (Hldi_μ0 : ldi_μ0 = ldi μ)
              (H0 : 3 * m <= b ^ (k + offset))
              (H1 : b ^ (k - offset) <= m + 1)
              (H2 : (0 <= μ < 2 ^ (256 * n)))
          : BarrettParametersCorrect x86_25519_Barrett
          := { props := props' ldi_modulus ldi_0 Hldi_modulus Hldi_0 }.
        Proof.
          assumption.
          vm_compute; reflexivity.
          vm_compute; clear; abstract intuition congruence.
          vm_compute; clear; abstract intuition congruence.
          assumption.
          assumption.
          vm_compute; exact I.
          { cbv [μ μ' x86_25519_Barrett ZBounded.decode_small BarrettBundled.ops ops' ZLikeOps_of_x86_64 ZLikeOps_of_x86_64_Factored ZLikeOps_of_x86_gen_Factored ZBounded.SmallT b k m offset].
            clear -props Hldi_μ0 n_pow_2 n_pos H2.
            abstract (
                subst ldi_μ0;
                assert (2^256 <= 2^(256 * n)) by (clear -n_pos; auto with zarith omega);
                rewrite decode_load_immediate
                  by solve [ exact _ | change (Z.of_nat 2) with 2%Z; rewrite n_pow_2; exact H2 ];
                reflexivity
              ). }
        Defined.
      End params_gen.
      Local Existing Instance x86_25519_Barrett.
      Local Existing Instance x86_25519_BarrettProofs.
      Definition ldi_modulus : Core.repeated_tuple x86.W 2 (Nat.log2 (256 / n)) := ldi modulus.
      Definition ldi_mod_inverse : Core.repeated_tuple x86.W 2 (Nat.log2 (256 / n)) := ldi (base^(2*k'0) / modulus).
      Definition barrett_reduce (x : tuple (Core.repeated_tuple x86.W 2 (Nat.log2 (256 / n))) 2)
        : Core.repeated_tuple x86.W 2 (Nat.log2 (256 / n))
        := dlet ldi_modulus' := ldi_modulus in
           dlet ldi_μ := ldi_mod_inverse in
           dlet ldi_0 := ldi 0 in
           let params := x86_25519_Barrett ldi_modulus' ldi_0 ldi_μ in
           barrett_reduce_function_bundled x.
    End gen.

    (*Section x86_64.
      Local Notation n := 64%nat.
      Context (ops : x86.instructions n) (props : x86.arithmetic ops).
      Lemma n64_pos : (0 < n)%Z. Proof. vm_compute; intuition congruence. Qed.
      Local Notation W := (tuple (tuple x86.W 2) 2) (* 256-bit words *).
      Local Arguments barrett_reduce / _ _ _ .
      Local Arguments Core.load_immediate_double / _ _ _ _.
      Local Arguments Z.modulo !_ !_ / .
      Local Arguments Z.pow_pos !_ !_ / .
      Local Arguments Z.div !_ !_ / .
      Local Arguments barrett_reduce_function_bundled : simpl never.
      Local Opaque Let_In.
      Time Definition barrett_reduce64 (x : tuple W 2) : W
        := Eval cv in @barrett_reduce 32 ops x.
      Eval cbv in barrett_reduce64.
      Definition barrett_reduce64'1 (x : tuple W 2) : W
        := Eval cbv [barrett_reduce64'0 tuple barrett_reduce_function_bundled barrett_reduce_function
                                        BarrettBundled.m BarrettBundled.b BarrettBundled.k BarrettBundled.offset BarrettBundled.μ' x86_25519_Barrett
                                        ZBounded.ConditionalSubtractModulus ZBounded.CarrySubSmall ZBounded.Mod_SmallBound ZBounded.Mod_SmallBound ZBounded.Mul ZBounded.DivBy_SmallBound ZBounded.DivBy_SmallerBound ZBounded.modulus_digits ZBounded.SmallT ZBounded.LargeT BarrettBundled.ops ZLikeOps_of_x86_gen_Factored]
          in @barrett_reduce64'0 x.
      Local Opaque Core.sub_with_carry_repeated_double Core.multiply_double_repeated_double
            Core.shift_right_doubleword_immediate_repeated_double
            Core.select_conditional_repeated_double.
      Local Arguments barrett_reduce64'1 / _.
      Definition barrett_reduce64'2 (x : tuple W 2) : W
        := Eval simpl in @barrett_reduce64'1 x.
      Local Transparent Core.sub_with_carry_repeated_double Core.multiply_double_repeated_double
            Core.shift_right_doubleword_immediate_repeated_double
            Core.select_conditional_repeated_double.
      Definition barrett_reduce64'3 (x : tuple W 2) : W
        := Eval cbv [barrett_reduce64'2
                       tuple Core.repeated_tuple tuple'
                       fst snd Interface.ldi Interface.muldw Interface.mulhwll Interface.mulhwhl Interface.mulhwhh Interface.shl Interface.shr Interface.or Interface.shrd Interface.adc Interface.subc Interface.selc Interface.adc Interface.subc
                       Core.select_conditional_repeated_double Core.selc_double Core.select_conditional_double
                       Core.multiply_double_repeated_double Core.mul_double_multiply Core.mul_double Core.mul_double_multiply_low_low Core.mul_double_multiply_high_low Core.mul_double_multiply_high_high
                       Core.shift_right_doubleword_immediate_repeated_double Core.shift_right_doubleword_immediate_double Core.shrd_double
                       Core.shlr_repeated_double
                       Core.shift_right_immediate_repeated_double Core.shift_left_immediate_repeated_double
                       Core.shift_left_immediate_double Core.shift_right_immediate_double
                       Core.shr_double Core.shl_double
                       Core.load_immediate_repeated_double Core.ldi_double Core.load_immediate_double
                       Core.ripple_carry_adc Core.ripple_carry_subc
                       Core.sub_with_carry_repeated_double Core.add_with_carry_repeated_double
                       Core.ripple_carry_tuple
                       Core.ripple_carry_tuple'
                       StripCF.shift_left_immediate_strip_CF StripCF.shift_right_immediate_strip_CF StripCF.bitwise_or_strip_CF StripCF.shift_right_doubleword_immediate_strip_CF StripCF.multiply_double_strip_CF
                       Nat.log2 Nat.div Nat.divmod Nat.pred Nat.log2_iter Core.ripple_carry_subc Z.of_nat Pos.of_succ_nat Z.pow Z.mul Z.eqb Z_eq_bool Pos.eqb Z.sub Z.ltb Z.leb Z.gtb Z.geb Pos.sub Pos.ltb Pos.leb Z.opp Z.add Pos.add Z.compare Z.pos_sub  Pos.compare Pos.compare_cont Z.pow_pos Pos.succ Pos.mul Pos.iter Z.succ_double Z.double Pos.pred_double
                       Z.modulo Z.div Z.div_eucl Z.pos_div_eucl Z.ltb Z.leb Pos.ltb Pos.leb Pos.compare Pos.compare_cont Z.compare fst snd Z.mul Pos.mul Z.add Pos.add Z.sub Z.opp Z.pos_sub Z.double Z.succ_double Pos.pred_double Z.pred_double]
          in @barrett_reduce64'2 x.
      Local Arguments barrett_reduce64'3 / _ .
    End x86_64.*)
  End gen_modulus.

  Section x86_64.
    Local Notation n := 64%nat.
    Section pre.
      Context (ops : x86.instructions n) (props : x86.arithmetic ops).
      Local Notation W := (tuple (tuple x86.W 2) 2) (* 256-bit words *).
      Time Definition barrett_reduce64' (x : tuple W 2) : W
        := Eval cbv -[Let_In] in @barrett_reduce modulusv 32 ops x. (* 25 s *)
    End pre.
    Context (ops : x86.instructions n) (props : x86.arithmetic ops).
    Local Notation W := (tuple (tuple x86.W 2) 2) (* 256-bit words *).
    Time Definition barrett_reduce64'1 (x : tuple W 2) : W
      := Eval cbv [barrett_reduce64' x86.eta_instructions] in @barrett_reduce64' (x86.eta_instructions ops) x.
    (* 25 s *)

    Print barrett_reduce64.

      Time Eval cbv -[Let_In] in @barrett_reduce64'1 n ops.


      Definition barrett_reduce64'4 (x : tuple W 2) : W.
      Proof.
        let ldiμ := constr:(ldi_mod_inverse modulusv 32 ops) in
        let ldiμv := (eval cbv [ldi_mod_inverse Core.load_immediate_repeated_double Core.ldi_double Core.load_immediate_double Nat.mul Nat.add Nat.div fst PeanoNat.Nat.divmod Nat.log2 Nat.log2_iter Nat.pred Core.repeated_tuple tuple tuple'] in ldiμ) in
        let arg := constr:(@Interface.ldi x86.W x86.ldi) in
        let ldiμv := match (eval pattern arg in ldiμv) with ?P _ => P end in
        let ldiμv := (eval vm_compute in ldiμv) in
        let ldiμv := (eval cbv beta in (ldiμv arg)) in
        let ldimodulus := constr:(ldi_modulus modulusv 32 ops) in
        let ldimodulusv := (eval cbv [ldi_modulus Core.load_immediate_repeated_double Core.ldi_double Core.load_immediate_double Nat.mul Nat.add Nat.div fst PeanoNat.Nat.divmod Nat.log2 Nat.log2_iter Nat.pred Core.repeated_tuple tuple tuple'] in ldimodulus) in
        let arg := constr:(@Interface.ldi x86.W x86.ldi) in
        let ldimodulusv := match (eval pattern arg in ldimodulusv) with ?P _ => P end in
        let ldimodulusv := (eval vm_compute in ldimodulusv) in
        let ldimodulusv := (eval cbv beta in (ldimodulusv arg)) in
        let v := constr:(@barrett_reduce64'3 modulusv ops x) in
        let v := (eval cbv beta iota delta [barrett_reduce64'3] in v) in
        let v := match v with
                 | appcontext v'[ldiμ]
                   => let v := context v'[ldiμv] in
                      v
                 end in
        let v := match v with
                 | appcontext v'[ldimodulus]
                   => let v := context v'[ldimodulusv] in
                      v
                 end in
        pose v.
        ldi_modulus modulusv 32 ops
        let
          := Eval simpl in @barrett_reduce64'3 x.
      Print barrett_reduce64.


      Eval cbv [ barrett_reduce64'3  fst snd    ] in barrett_reduce64'3.

      StripCF.multiply_double_strip_CF
      Lemma modulus_in_range : (0 <= modulus < 2 ^ 256)%Z. Proof. vm_compute; intuition congruence. Qed.


  Section params_64.
    Import BarrettBundled.
    Let offset' := Eval compute in ((256 - smaller_bound_exp) / 2)%Z.
    Let k' := Eval compute in ((256 - offset') / Z.log2 base)%Z.
    Let μ0 := Eval compute in (base ^ (2 * k') / modulus)%Z.
    Local Instance x86_25519_Barrett ldi_modulus ldi_0 : BarrettParameters
      := { m := modulus;
           b := base;
           k := k';
           offset := offset';
           ops := ops' ldi_modulus ldi_0;
           μ' := ldi μ0 }.
    Local Instance x86_25519_BarrettProofs
          ldi_modulus ldi_0 Hldi_modulus Hldi_0
      : BarrettParametersCorrect (x86_25519_Barrett ldi_modulus ldi_0)
      := { props := props' ldi_modulus ldi_0 Hldi_modulus Hldi_0 }.
    Proof.
      vm_compute; reflexivity.
      vm_compute; reflexivity.
      vm_compute; clear; abstract intuition congruence.
      vm_compute; clear; abstract intuition congruence.
      vm_compute; clear; abstract intuition congruence.
      vm_compute; clear; abstract intuition congruence.
      vm_compute; exact I.
      { cbv [μ μ' x86_25519_Barrett ZBounded.decode_small BarrettBundled.ops ops' ZLikeOps_of_x86_64 ZLikeOps_of_x86_64_Factored ZLikeOps_of_x86_gen_Factored ZBounded.SmallT b k m offset].
        clear -props.
        abstract (
            rewrite decode_load_immediate by solve [ exact _ | vm_compute; intuition congruence ];
            vm_compute; reflexivity
          ). }
    Qed.
  End params_64.
  Local Existing Instance x86_25519_Barrett.
  Local Existing Instance x86_25519_BarrettProofs.

  Definition barrett_reduce (x : tuple W 2) : W
    := dlet ldi_modulus := ldi modulus in
       dlet ldi_0 := ldi 0 in
       let params := x86_25519_Barrett ldi_modulus ldi_0 in
       barrett_reduce_function_bundled x.

  Axiom admit : forall {T}, T.
  Definition SRep := tuple x86.W (256/n).
  Definition SRepEq : Relation_Definitions.relation SRep := Logic.eq.
  Local Instance SRepEquiv : RelationClasses.Equivalence SRepEq := _.
  Definition WofSRep (x : SRep) : W
    := let '(a, b, c, d) := x in ((a, b), (c, d)).
  Definition SRepofW (x : W) : SRep
    := let '((a, b), (c, d)) := x in (a, b, c, d).
  Local Coercion WofSRep : SRep >-> W.
  Local Coercion SRepofW : W >-> SRep.
  Local Opaque Z.of_N Word.wordToN Word.split1 Word.split2.
  Local Opaque Let_In.
  Local Arguments Core.load_immediate_double / _ _ _ _.
  Local Arguments Z.pow_pos !_ !_ / .
  Local Arguments Z.div !_ !_ / .
  Local Arguments Z.modulo !_ !_ / .
  Local Arguments SRepofW / _ .
  Local Arguments barrett_reduce : simpl never.
  Definition SRepDecModL'_helper_ldi' : Z -> W
    := Eval cbv [Core.ldi_double Z.mul Z.of_nat Core.load_immediate_double Pos.of_succ_nat Pos.mul Pos.succ Z.pow Z.pow_pos Pos.iter] in
        ldi.
  Local Arguments SRepDecModL'_helper_ldi' / _.
  Definition SRepDecModL'_helper_ldi : Z -> W
    := Eval simpl in  SRepDecModL'_helper_ldi'.
  Local Arguments SRepDecModL'_helper_ldi : simpl never.
  Definition SRepDecModL' : Word.word (256 + 256) -> SRep (* TODO(@andres-erbsen): Did I get the right sense of split1, split2? *)
    := Eval simpl in
        fun w => dlet w' := (SRepDecModL'_helper_ldi (Z.of_N (Word.wordToN (Word.split1 _ _ w))),
                             SRepDecModL'_helper_ldi (Z.of_N (Word.wordToN (Word.split2 _ _ w))))%core in
             SRepofW (barrett_reduce w').
  Definition SRepDecModL'' : Word.word (256 + 256) -> SRep
    := Eval cbv [SRepDecModL' barrett_reduce barrett_reduce_function_bundled barrett_reduce_function ZBounded.ConditionalSubtractModulus ZBounded.ConditionalSubtractModulus ZBounded.CarrySubSmall ZBounded.Mod_SmallBound ZBounded.Mul ZBounded.DivBy_SmallBound ZBounded.DivBy_SmallerBound BarrettBundled.μ' ZBounded.modulus_digits BarrettBundled.ops BarrettBundled.k BarrettBundled.offset BarrettBundled.b x86_25519_Barrett ops' ZLikeOps_of_x86_64_Factored ZLikeOps_of_x86_gen_Factored
                              Nat.log2 Nat.div Nat.divmod Nat.pred Nat.log2_iter Core.ripple_carry_subc Z.of_nat Pos.of_succ_nat Z.pow Z.mul Z.eqb Z_eq_bool Pos.eqb Z.sub Z.ltb Z.leb Z.gtb Z.geb Pos.sub Pos.ltb Pos.leb Z.opp Z.add Pos.add Z.compare Z.pos_sub  Pos.compare Pos.compare_cont Z.pow_pos Pos.succ Pos.mul Pos.iter Z.succ_double Z.double Pos.pred_double] in
        SRepDecModL'.
  Local Arguments SRepDecModL'' / _ .
  Definition SRepDecModL''' : Word.word (256 + 256) -> SRep
    := Eval cbv [SRepDecModL'' Core.load_immediate_repeated_double Core.ldi_double Core.load_immediate_double
                               Core.multiply_double_repeated_double StripCF.multiply_double_strip_CF Core.mul_double_multiply Core.mul_double Core.mul_double_multiply_high_low Core.mul_double_multiply_high_high Core.mul_double_multiply_low_low
                               Nat.log2 Nat.div Nat.divmod Nat.pred Nat.log2_iter Core.ripple_carry_subc Z.of_nat Pos.of_succ_nat Z.pow Z.mul Z.eqb Z_eq_bool Pos.eqb Z.sub Z.ltb Z.leb Z.gtb Z.geb Pos.sub Pos.ltb Pos.leb Z.opp Z.add Pos.add Z.compare Z.pos_sub  Pos.compare Pos.compare_cont Z.pow_pos Pos.succ Pos.mul Pos.iter Z.succ_double Z.double Pos.pred_double] in
        SRepDecModL''.
  Local Arguments SRepDecModL''' / _.
  Definition SRepDecModL'''' : Word.word (256 + 256) -> SRep
    := Eval cbn [SRepDecModL''' fst snd Interface.ldi Interface.muldw Interface.mulhwll Interface.mulhwhl Interface.mulhwhh
                                Nat.log2 Nat.div Nat.divmod Nat.pred Nat.log2_iter Core.ripple_carry_subc Z.of_nat Pos.of_succ_nat Z.pow Z.mul Z.eqb Z_eq_bool Pos.eqb Z.sub Z.ltb Z.leb Z.gtb Z.geb Pos.sub Pos.ltb Pos.leb Z.opp Z.add Pos.add Z.compare Z.pos_sub  Pos.compare Pos.compare_cont Z.pow_pos Pos.succ Pos.mul Pos.iter Z.succ_double Z.double Pos.pred_double
                                Z.modulo Z.div] in
        SRepDecModL'''.
  Definition SRepDecModL''''' : Word.word (256 + 256) -> SRep
    := Eval cbv [SRepDecModL'''' Core.shr_double Core.shl_double Core.shift_left_immediate_double Core.shift_right_immediate_double Core.shift_left_immediate_repeated_double Core.shift_right_immediate_repeated_double Core.shlr_repeated_double StripCF.shift_left_immediate_strip_CF StripCF.shift_right_immediate_strip_CF StripCF.bitwise_or_strip_CF] in
        SRepDecModL''''.
  Local Arguments SRepDecModL''''' / _.
  Definition SRepDecModL'''''' : Word.word (256 + 256) -> SRep
    := Eval cbn [SRepDecModL''''' fst snd Interface.ldi Interface.muldw Interface.mulhwll Interface.mulhwhl Interface.mulhwhh Interface.shl Interface.shr Interface.or Interface.shrd
                                Nat.log2 Nat.div Nat.divmod Nat.pred Nat.log2_iter Core.ripple_carry_subc Z.of_nat Pos.of_succ_nat Z.pow Z.mul Z.eqb Z_eq_bool Pos.eqb Z.sub Z.ltb Z.leb Z.gtb Z.geb Pos.sub Pos.ltb Pos.leb Z.opp Z.add Pos.add Z.compare Z.pos_sub  Pos.compare Pos.compare_cont Z.pow_pos Pos.succ Pos.mul Pos.iter Z.succ_double Z.double Pos.pred_double
                                Z.modulo Z.div] in
        SRepDecModL'''''.
  Definition SRepDecModL''''''' : Word.word (256 + 256) -> SRep
    := Eval cbv [SRepDecModL'''''' Core.bitwise_or_repeated_double  Core.or_double Core.shift_right_doubleword_immediate_repeated_double] in
        SRepDecModL''''''.
  Local Arguments SRepDecModL''''''' / _.
  Definition SRepDecModL'''''''' : Word.word (256 + 256) -> SRep
    := Eval cbn [SRepDecModL''''''' fst snd Interface.ldi Interface.muldw Interface.mulhwll Interface.mulhwhl Interface.mulhwhh Interface.shl Interface.shr Interface.or Interface.shrd
                                Nat.log2 Nat.div Nat.divmod Nat.pred Nat.log2_iter Core.ripple_carry_subc Z.of_nat Pos.of_succ_nat Z.pow Z.mul Z.eqb Z_eq_bool Pos.eqb Z.sub Z.ltb Z.leb Z.gtb Z.geb Pos.sub Pos.ltb Pos.leb Z.opp Z.add Pos.add Z.compare Z.pos_sub  Pos.compare Pos.compare_cont Z.pow_pos Pos.succ Pos.mul Pos.iter Z.succ_double Z.double Pos.pred_double
                                Z.modulo Z.div] in
        SRepDecModL'''''''.
  Print SRepDecModL'''''''.
    Definition SRepDecModL''''' : Word.word (256 + 256) -> SRep
    := Eval cbv [SRepDecModL'''' StripCF.shift_left_immediate_strip_CF StripCF.shift_right_immediate_strip_CF StripCF.bitwise_or_strip_CF
                                 Z.modulo Z.div_eucl Z.pos_div_eucl Z.ltb Z.leb Pos.ltb Pos.leb Pos.compare Pos.compare_cont Z.compare fst snd Z.mul Pos.mul Z.add Pos.add Z.sub Z.opp Z.pos_sub Z.double Z.succ_double Pos.pred_double Z.pred_double]
      in SRepDecModL''''.
  Print SRepDecModL'''''.
  Set Printing Depth 1000000.
  Eval cbn [Z.modulo Z.div_eucl Z.pos_div_eucl Z.ltb Z.leb Pos.ltb Pos.leb Pos.compare Pos.compare_cont Z.compare fst snd Z.mul Pos.mul Z.add Pos.add Z.sub Z.opp Z.pos_sub Z.double Z.succ_double Pos.pred_double Z.pred_double] in ((28948022309329048855892746252171976963206526895300651595720988250814747816012
                                                                   mod 340282366920938463463374607431768211456) mod 18446744073709551616)%Z.
  Print SRepDecModL''''''''.
  Print SRepDecModL''''''.
  Print SRepDecModL''''.




  Local Arguments SRepDecModL' / _.

  Definition SRepDecModL''
    := Eval cbv [SRepDecModL' ZLikeOps_of_x86_gen_Factored Nat.log2 Nat.div Nat.divmod Nat.pred Nat.log2_iter Core.ripple_carry_subc Z.of_nat Pos.of_succ_nat Z.pow Z.mul Z.eqb Z_eq_bool Pos.eqb Z.sub Z.ltb Z.leb Z.gtb Z.geb Pos.sub Pos.ltb Pos.leb Z.opp Z.add Pos.add Z.compare Z.pos_sub  Pos.compare Pos.compare_cont Z.pow_pos Pos.succ Pos.mul Pos.iter ] in SRepDecModL'.
  Print SRepDecModL''.
  Definition SRepDecModL'''
    := Eval cbv [SRepDecModL''
                   fst snd Interface.or Interface.subc Interface.ldi Interface.muldw Interface.shrd Interface.selc Interface.mulhwll Interface.mulhwhl Interface.mulhwhh Interface.shl Interface.shr Interface.adc
                   Core.ripple_carry_tuple Core.ripple_carry_tuple' Core.sub_with_carry_repeated_double Core.multiply_double_repeated_double Core.mul_double_multiply Core.mul_double Core.mul_double_multiply_low_low Core.mul_double_multiply_high_high Core.mul_double_multiply_high_low StripCF.multiply_double_strip_CF Core.shift_right_doubleword_immediate_repeated_double Core.shrd_double Core.select_conditional_repeated_double Core.shift_right_doubleword_immediate_double Core.selc_double StripCF.shift_right_doubleword_immediate_strip_CF Core.load_immediate_repeated_double Core.shl_double Core.shr_double Core.ldi_double Core.shift_left_immediate_double Core.shift_right_immediate_double Core.load_immediate_double Core.shift_left_immediate_repeated_double Core.bitwise_or_repeated_double Core.shift_right_immediate_repeated_double Core.shlr_repeated_double Core.ripple_carry_adc Core.add_with_carry_repeated_double Core.select_conditional_double
                   Nat.log2 Nat.div Nat.divmod Nat.pred Nat.log2_iter Core.ripple_carry_subc Z.of_nat Pos.of_succ_nat Z.pow Z.mul Z.eqb Z_eq_bool Pos.eqb Z.sub Z.ltb Z.leb Z.gtb Z.geb Pos.sub Pos.ltb Pos.leb Z.opp Z.add Pos.add Z.compare Z.pos_sub  Pos.compare Pos.compare_cont Z.pow_pos Pos.succ Pos.mul Pos.iter Z.succ_double Z.double Pos.pred_double]
      in SRepDecModL''.
  Print SRepDecModL'''.

 ]
                          fst snd Interface.or Interface.subc Interface.ldi Interface.muldw Interface.shrd Interface.selc Interface.mulhwll Interface.mulhwhl Interface.mulhwhh Interface.shl Interface.shr Interface.adc





  Print SRepDecModL'.
  ZBounded.Mul ZBounded.DivBy_SmallBound




  (* TODO(jadep):what's S2Rep? *)
  (*Lemma SRepDecModL_Correct : forall w : Word.word (b + b), SRepEq (S2Rep (ModularArithmetic.F.of_nat l (Word.wordToNat w))) (SRepDecModL w).*)
  Check sign_valid.
  Arguments Algebra.group : clear implicits.
  Check @sign_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ ed25519.
  Check @verify_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ ed25519.
