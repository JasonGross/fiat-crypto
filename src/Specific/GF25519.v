Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import Coq.Lists.List Crypto.Util.ListUtil.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Algebra.
Import ListNotations.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Local Open Scope Z.

(* BEGIN precomputation. *)

Definition modulus : Z := Eval compute in 2^255 - 19.
Lemma prime_modulus : prime modulus. Admitted.
Definition int_width := 32%Z.

Instance params25519 : PseudoMersenneBaseParams modulus.
  construct_params prime_modulus 10%nat 255.
Defined.

Definition fe25519 := Eval compute in (tuple Z (length limb_widths)).

Definition mul2modulus : fe25519 :=
  Eval compute in (from_list_default 0%Z (length limb_widths) (construct_mul2modulus params25519)).

Instance subCoeff : SubtractionCoefficient.
  apply Build_SubtractionCoefficient with (coeff := mul2modulus).
  vm_decide.
Defined.

Instance carryChain : CarryChain limb_widths.
  apply Build_CarryChain with (carry_chain := (rev [0;1;2;3;4;5;6;7;8;9;0;1])%nat).
  intros.
  repeat (destruct H as [|H]; [subst; vm_compute; repeat constructor | ]).
  contradiction H.
Defined.

Definition freezePreconditions25519 : freezePreconditions params25519 int_width.
Proof.
  constructor; compute_preconditions.
Defined.

(* Wire format for [pack] and [unpack] *)
Definition wire_widths := Eval compute in (repeat 32 7 ++ 31 :: nil).

Definition wire_digits := Eval compute in (tuple Z (length wire_widths)).

Lemma wire_widths_nonneg : forall w, In w wire_widths -> 0 <= w.
Proof.
  intros.
  repeat (destruct H as [|H]; [subst; vm_compute; congruence | ]).
  contradiction H.
Qed.

Lemma bits_eq : sum_firstn limb_widths (length limb_widths) = sum_firstn wire_widths (length wire_widths).
Proof.
  reflexivity.
Qed.

Lemma modulus_gt_2 : 2 < modulus. Proof. cbv; congruence. Qed.

(* Temporarily, we'll use addition chains equivalent to double-and-add. This is pending
   finding the real, more optimal chains from previous work. *)
Fixpoint pow2Chain'' p (pow2_index acc_index : nat) chain_acc : list (nat * nat) :=
  match p with
  | xI p' => pow2Chain'' p' 1 0
               (chain_acc ++ (pow2_index, pow2_index) :: (0%nat, S acc_index) :: nil)
  | xO p' => pow2Chain'' p' 0 (S acc_index)
               (chain_acc ++ (pow2_index, pow2_index)::nil)
  | xH => (chain_acc ++ (pow2_index, pow2_index) :: (0%nat, S acc_index) :: nil)
  end.

Fixpoint pow2Chain' p index  :=
  match p with
  | xI p' => pow2Chain'' p' 0 0 (repeat (0,0)%nat index)
  | xO p' => pow2Chain' p' (S index)
  | xH => repeat (0,0)%nat index
  end.

Definition pow2_chain p :=
  match p with
  | xH => nil
  | _ => pow2Chain' p 0
  end.

Definition invChain := Eval compute in pow2_chain (Z.to_pos (modulus - 2)).

Instance inv_ec : ExponentiationChain (modulus - 2).
  apply Build_ExponentiationChain with (chain := invChain).
  reflexivity.
Defined.

(* Note : use caution copying square root code to other primes. The (modulus / 8 + 1) chains are
   for primes that are 5 mod 8; if the prime is 3 mod 4 then use (modulus / 4 + 1). *)
Definition sqrtChain := Eval compute in pow2_chain (Z.to_pos (modulus / 8 + 1)).

Instance sqrt_ec : ExponentiationChain (modulus / 8 + 1).
  apply Build_ExponentiationChain with (chain := sqrtChain).
  reflexivity.
Defined.

Arguments chain {_ _ _} _.

(* END precomputation *)

(* Precompute constants *)
Definition k_ := Eval compute in k.
Definition k_subst : k = k_ := eq_refl k_.

Definition c_ := Eval compute in c.
Definition c_subst : c = c_ := eq_refl c_.

Definition one_ := Eval compute in one.
Definition one_subst : one = one_ := eq_refl one_.

Definition zero_ := Eval compute in zero.
Definition zero_subst : zero = zero_ := eq_refl zero_.

Definition modulus_digits_ := Eval compute in ModularBaseSystemList.modulus_digits.
Definition modulus_digits_subst : ModularBaseSystemList.modulus_digits = modulus_digits_ := eq_refl modulus_digits_.

Local Opaque Z.shiftr Z.shiftl Z.land Z.mul Z.add Z.sub Z.lor Let_In Z.eqb Z.ltb Z.leb andb.

Definition app_7 {T} (f : wire_digits) (P : wire_digits -> T) : T.
Proof.
  cbv [wire_digits] in *.
  set (f0 := f).
  repeat (let g := fresh "g" in destruct f as [f g]).
  apply P.
  apply f0.
Defined.

Definition app_7_correct {T} f (P : wire_digits -> T) : app_7 f P = P f.
Proof.
  intros.
  cbv [wire_digits] in *.
  repeat match goal with [p : (_*Z)%type |- _ ] => destruct p end.
  reflexivity.
Qed.

Definition app_10 {T} (f : fe25519) (P : fe25519 -> T) : T.
Proof.
  cbv [fe25519] in *.
  set (f0 := f).
  repeat (let g := fresh "g" in destruct f as [f g]).
  apply P.
  apply f0.
Defined.

Definition app_10_correct {T} f (P : fe25519 -> T) : app_10 f P = P f.
Proof.
  intros.
  cbv [fe25519] in *.
  repeat match goal with [p : (_*Z)%type |- _ ] => destruct p end.
  reflexivity.
Qed.

Definition appify2 {T} (op : fe25519 -> fe25519 -> T) (f g : fe25519) :=
  app_10 f (fun f0 => (app_10 g (fun g0 => op f0 g0))).

Lemma appify2_correct : forall {T} op f g, @appify2 T op f g = op f g.
Proof.
  intros. cbv [appify2].
  etransitivity; apply app_10_correct.
Qed.

Definition add_sig (f g : fe25519) :
  { fg : fe25519 | fg = add_opt f g}.
Proof.
  eexists.
  rewrite <-(@appify2_correct fe25519).
  cbv.
  reflexivity.
Defined.

Definition add (f g : fe25519) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig add_sig] in
  proj1_sig (add_sig f g).

Definition add_correct (f g : fe25519)
  : add f g = add_opt f g :=
  Eval cbv beta iota delta [proj1_sig add_sig] in
  proj2_sig (add_sig f g).

Definition sub_sig (f g : fe25519) :
  { fg : fe25519 | fg = sub_opt f g}.
Proof.
  eexists.
  rewrite <-(@appify2_correct fe25519).
  cbv.
  reflexivity.
Defined.

Definition sub (f g : fe25519) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig sub_sig] in
  proj1_sig (sub_sig f g).

Definition sub_correct (f g : fe25519)
  : sub f g = sub_opt f g :=
  Eval cbv beta iota delta [proj1_sig sub_sig] in
  proj2_sig (sub_sig f g).

(* For multiplication, we add another layer of definition so that we can
   rewrite under the [let] binders. *)
Definition mul_simpl_sig (f g : fe25519) :
  { fg : fe25519 | fg = carry_mul_opt k_ c_ f g}.
Proof.
  cbv [fe25519] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  eexists.
  cbv. (* N.B. The slow part of this is computing with [Z_div_opt].
               It would be much faster if we could take advantage of
               the form of [base_from_limb_widths] when doing
               division, so we could do subtraction instead. *)
  autorewrite with zsimplify_fast.
  reflexivity.
Defined.

Definition mul_simpl (f g : fe25519) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig mul_simpl_sig] in
  let '(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9) := f in
  let '(g0, g1, g2, g3, g4, g5, g6, g7, g8, g9) := g in
  proj1_sig (mul_simpl_sig (f0, f1, f2, f3, f4, f5, f6, f7, f8, f9)
                           (g0, g1, g2, g3, g4, g5, g6, g7, g8, g9)).

Definition mul_simpl_correct (f g : fe25519)
  : mul_simpl f g = carry_mul_opt k_ c_ f g.
Proof.
  pose proof (proj2_sig (mul_simpl_sig f g)).
  cbv [fe25519] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  assumption.
Qed.

Definition mul_sig (f g : fe25519) :
  { fg : fe25519 | fg = carry_mul_opt k_ c_ f g}.
Proof.
  eexists.
  rewrite <-mul_simpl_correct.
  rewrite <-(@appify2_correct fe25519).
  cbv.
  reflexivity.
Defined.

Definition mul (f g : fe25519) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig mul_sig] in
  proj1_sig (mul_sig f g).

Definition mul_correct (f g : fe25519)
  : mul f g = carry_mul_opt k_ c_ f g :=
  Eval cbv beta iota delta [proj1_sig add_sig] in
  proj2_sig (mul_sig f g).

Definition opp_sig (f : fe25519) :
  { g : fe25519 | g = opp_opt f }.
Proof.
  eexists.
  cbv [opp_opt].
  rewrite <-sub_correct.
  rewrite zero_subst.
  cbv [sub].
  reflexivity.
Defined.

Definition opp (f : fe25519) : fe25519
  := Eval cbv beta iota delta [proj1_sig opp_sig] in proj1_sig (opp_sig f).

Definition opp_correct (f : fe25519)
  : opp f = opp_opt f
  := Eval cbv beta iota delta [proj2_sig add_sig] in proj2_sig (opp_sig f).

Definition pow (f : fe25519) chain := fold_chain_opt one_ mul chain [f].

Lemma pow_correct (f : fe25519) : forall chain, pow f chain = pow_opt k_ c_ one_ f chain.
Proof.
  cbv [pow pow_opt]; intros.
  rewrite !fold_chain_opt_correct.
  apply Proper_fold_chain; try reflexivity.
  intros; subst; apply mul_correct.
Qed.

(* Now that we have [pow], we can compute sqrt of -1 for use
   in sqrt function (this is not needed unless the prime is
   5 mod 8) *)
Local Transparent Z.shiftr Z.shiftl Z.land Z.mul Z.add Z.sub Z.lor Let_In Z.eqb Z.ltb andb.

Definition sqrt_m1 := Eval vm_compute in (pow (encode (F.of_Z _ 2)) (pow2_chain (Z.to_pos ((modulus - 1) / 4)))).

Lemma sqrt_m1_correct : rep (mul sqrt_m1 sqrt_m1) (F.opp 1%F).
Proof.
  cbv [rep].
  apply F.eq_to_Z_iff.
  vm_compute.
  reflexivity.
Qed.

Local Opaque Z.shiftr Z.shiftl Z.land Z.mul Z.add Z.sub Z.lor Let_In Z.eqb Z.ltb andb.

Definition inv_sig (f : fe25519) :
  { g : fe25519 | g = inv_opt k_ c_ one_ f }.
Proof.
  eexists; cbv [inv_opt].
  rewrite <-pow_correct.
  cbv - [mul].
  reflexivity.
Defined.

Definition inv (f : fe25519) : fe25519
  := Eval cbv beta iota delta [proj1_sig inv_sig] in proj1_sig (inv_sig f).

Definition inv_correct (f : fe25519)
  : inv f = inv_opt k_ c_ one_ f
  := Eval cbv beta iota delta [proj2_sig inv_sig] in proj2_sig (inv_sig f).

Definition mbs_field := modular_base_system_field modulus_gt_2.

Import Morphisms.

Lemma field25519 : @field fe25519 eq zero one opp add sub mul inv div.
Proof.
  pose proof (Equivalence_Reflexive : Reflexive eq).
  eapply (Field.equivalent_operations_field (fieldR := mbs_field)).
  Grab Existential Variables.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + intros; rewrite mul_correct.
    rewrite carry_mul_opt_correct by auto using k_subst, c_subst.
    cbv [eq].
    rewrite carry_mul_rep by reflexivity.
    rewrite mul_rep; reflexivity.
  + intros; rewrite sub_correct, sub_opt_correct; reflexivity.
  + intros; rewrite add_correct, add_opt_correct; reflexivity.
  + intros; rewrite inv_correct, inv_opt_correct; reflexivity.
  + intros; rewrite opp_correct, opp_opt_correct; reflexivity.
Qed.

Lemma homomorphism_F25519 :
  @Ring.is_homomorphism
    (F modulus) Logic.eq F.one F.add F.mul
    fe25519 eq one add mul encode.
Proof.
  econstructor.
  + econstructor; [ | apply encode_Proper].
    intros; cbv [eq].
    rewrite add_correct, add_opt_correct, add_rep; apply encode_rep.
  + intros; cbv [eq].
    rewrite mul_correct, carry_mul_opt_correct, carry_mul_rep
      by auto using k_subst, c_subst, encode_rep.
    apply encode_rep.
  + reflexivity.
Qed.

Definition ge_modulus_sig (f : fe25519) :
  { b : bool | b = ge_modulus_opt (to_list 10 f) }.
Proof.
  cbv [fe25519] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  eexists; cbv [ge_modulus_opt].
  rewrite !modulus_digits_subst.
  cbv.
  reflexivity.
Defined.

Definition ge_modulus (f : fe25519) : bool :=
  Eval cbv beta iota delta [proj1_sig ge_modulus_sig] in
    let '(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9) := f in
    proj1_sig (ge_modulus_sig (f0, f1, f2, f3, f4, f5, f6, f7, f8, f9)).

Definition ge_modulus_correct (f : fe25519) :
  ge_modulus f = ge_modulus_opt (to_list 10 f).
Proof.
  pose proof (proj2_sig (ge_modulus_sig f)).
  cbv [fe25519] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  assumption.
Defined.

Definition freeze_sig (f : fe25519) :
  { f' : fe25519 | f' = from_list_default 0 10 (freeze_opt c_ (to_list 10 f)) }.
Proof.
  cbv [fe25519] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  eexists; cbv [freeze_opt].
  cbv [to_list to_list'].
  cbv [conditional_subtract_modulus_opt].
  rewrite !modulus_digits_subst.
  cbv - [from_list_default].
  (* TODO(jgross,jadep): use Reflective linearization here? *)
  repeat (
       set_evars; rewrite app_Let_In_nd; subst_evars;
       eapply Proper_Let_In_nd_changebody; [reflexivity|intro]).
  cbv [from_list_default from_list_default'].
  reflexivity.
Defined.

Definition freeze (f : fe25519) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig freeze_sig] in
    let '(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9) := f in
    proj1_sig (freeze_sig (f0, f1, f2, f3, f4, f5, f6, f7, f8, f9)).

Definition freeze_correct (f : fe25519)
  : freeze f = from_list_default 0 10 (freeze_opt c_ (to_list 10 f)).
Proof.
  pose proof (proj2_sig (freeze_sig f)).
  cbv [fe25519] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  assumption.
Defined.

Definition fieldwiseb_sig (f g : fe25519) :
  { b | b = @fieldwiseb Z Z 10 Z.eqb f g }.
Proof.
  cbv [fe25519] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  eexists.
  cbv.
  reflexivity.
Defined.

Definition fieldwiseb (f g : fe25519) : bool
  := Eval cbv beta iota delta [proj1_sig fieldwiseb_sig] in proj1_sig (fieldwiseb_sig f g).

Definition fieldwiseb_correct (f g : fe25519)
  : fieldwiseb f g = @Tuple.fieldwiseb Z Z 10 Z.eqb f g
  := Eval cbv beta iota delta [proj2_sig fieldwiseb_sig] in proj2_sig (fieldwiseb_sig f g).

Definition eqb_sig (f g : fe25519) :
  { b | b = eqb f g }.
Proof.
  cbv [eqb].
  cbv [fe25519] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  eexists.
  cbv [ModularBaseSystem.freeze].
  rewrite <-!from_list_default_eq with (d := 0).
  rewrite <-!(freeze_opt_correct c_) by auto using length_to_list.
  rewrite <-!freeze_correct.
  rewrite <-fieldwiseb_correct.
  reflexivity.
Defined.

Definition eqb (f g : fe25519) : bool
  := Eval cbv beta iota delta [proj1_sig eqb_sig] in proj1_sig (eqb_sig f g).

Definition eqb_correct (f g : fe25519)
  : eqb f g = ModularBaseSystem.eqb f g
  := Eval cbv beta iota delta [proj2_sig eqb_sig] in proj2_sig (eqb_sig f g).

Definition sqrt_sig (f : fe25519) :
  { f' : fe25519 | f' = sqrt_5mod8_opt k_ c_ one_ sqrt_m1 f}.
Proof.
  eexists.
  cbv [sqrt_5mod8_opt].
  apply Proper_Let_In_nd_changebody; [reflexivity|intro].
  set_evars. rewrite <-!mul_correct, <-eqb_correct. subst_evars.
  reflexivity.
Defined.

Definition sqrt (f : fe25519) : fe25519
  := Eval cbv beta iota delta [proj1_sig sqrt_sig] in proj1_sig (sqrt_sig f).

Definition sqrt_correct (f : fe25519)
  : sqrt f = sqrt_5mod8_opt k_ c_ one_ sqrt_m1 f
  := Eval cbv beta iota delta [proj2_sig sqrt_sig] in proj2_sig (sqrt_sig f).

Definition pack_simpl_sig (f : fe25519) :
  { f' | f' = pack_opt params25519 wire_widths_nonneg bits_eq f }.
Proof.
  cbv [fe25519] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  eexists.
  cbv [pack_opt].
  repeat (rewrite <-convert'_opt_correct;
          cbv - [from_list_default_opt Conversion.convert']).
  repeat progress rewrite ?Z.shiftl_0_r, ?Z.shiftr_0_r, ?Z.land_0_l, ?Z.lor_0_l, ?Z.land_same_r.
  cbv [from_list_default_opt].
  reflexivity.
Defined.

Definition pack_simpl (f : fe25519) :=
  Eval cbv beta iota delta [proj1_sig pack_simpl_sig] in
    let '(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9) := f in
    proj1_sig (pack_simpl_sig (f0, f1, f2, f3, f4, f5, f6, f7, f8, f9)).

Definition pack_simpl_correct (f : fe25519)
  : pack_simpl f = pack_opt params25519 wire_widths_nonneg bits_eq f.
Proof.
  pose proof (proj2_sig (pack_simpl_sig f)).
  cbv [fe25519] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  assumption.
Qed.

Definition pack_sig (f : fe25519) :
  { f' | f' = pack_opt params25519 wire_widths_nonneg bits_eq f }.
Proof.
  eexists.
  rewrite <-pack_simpl_correct.
  rewrite <-(@app_10_correct wire_digits).
  cbv.
  reflexivity.
Defined.

Definition pack (f : fe25519) : wire_digits :=
  Eval cbv beta iota delta [proj1_sig pack_sig] in proj1_sig (pack_sig f).

Definition pack_correct (f : fe25519)
  : pack f = pack_opt params25519 wire_widths_nonneg bits_eq f
  := Eval cbv beta iota delta [proj2_sig pack_sig] in proj2_sig (pack_sig f).

Definition unpack_simpl_sig (f : wire_digits) :
  { f' | f' = unpack_opt params25519 wire_widths_nonneg bits_eq f }.
Proof.
  cbv [wire_digits] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  eexists.
  cbv [unpack_opt].
  repeat (
      rewrite <-convert'_opt_correct;
      cbv - [from_list_default_opt Conversion.convert']).
  repeat progress rewrite ?Z.shiftl_0_r, ?Z.shiftr_0_r, ?Z.land_0_l, ?Z.lor_0_l, ?Z.land_same_r.
  cbv [from_list_default_opt].
  reflexivity.
Defined.

Definition unpack_simpl (f : wire_digits) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig unpack_simpl_sig] in
    let '(f0, f1, f2, f3, f4, f5, f6, f7) := f in
    proj1_sig (unpack_simpl_sig (f0, f1, f2, f3, f4, f5, f6, f7)).

Definition unpack_simpl_correct (f : wire_digits)
  : unpack_simpl f = unpack_opt params25519 wire_widths_nonneg bits_eq f.
Proof.
  pose proof (proj2_sig (unpack_simpl_sig f)).
  cbv [wire_digits] in *.
  repeat match goal with p : (_ * Z)%type |- _ => destruct p end.
  assumption.
Qed.

Definition unpack_sig (f : wire_digits) :
  { f' | f' = unpack_opt params25519 wire_widths_nonneg bits_eq f }.
Proof.
  eexists.
  rewrite <-unpack_simpl_correct.
  rewrite <-(@app_7_correct fe25519).
  cbv.
  reflexivity.
Defined.

Definition unpack (f : wire_digits) : fe25519 :=
  Eval cbv beta iota delta [proj1_sig unpack_sig] in proj1_sig (unpack_sig f).

Definition unpack_correct (f : wire_digits)
  : unpack f = unpack_opt params25519 wire_widths_nonneg bits_eq f
  := Eval cbv beta iota delta [proj2_sig pack_sig] in proj2_sig (unpack_sig f).


Require Import Coq.omega.Omega Coq.micromega.Psatz.
Require Import Coq.PArith.BinPos Coq.Lists.List.
Require Import Crypto.Reflection.Named.Syntax.
Require Import Crypto.Reflection.Named.Compile.
Require Import Crypto.Reflection.Named.RegisterAssign.
Require Import Crypto.Reflection.Syntax.
Require Export Crypto.Reflection.Reify.
Require Import Crypto.Reflection.InputSyntax.
Require Import Crypto.Reflection.CommonSubexpressionElimination.
Require Crypto.Reflection.Linearize Crypto.Reflection.Inline.
Require Import Crypto.Reflection.WfReflective.
Require Import Crypto.Reflection.Conversion.

Print mul.
Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.
Scheme Equality for Z.
Inductive base_type := TZ.
Definition interp_base_type (v : base_type) : Type :=
  match v with
  | TZ => Z
  end.
Local Notation tZ := (Tbase TZ).
Inductive op : flat_type base_type -> flat_type base_type -> Type :=
| Add : op (Prod tZ tZ) tZ
| Mul : op (Prod tZ tZ) tZ
| Sub : op (Prod tZ tZ) tZ
| Shl : op (Prod tZ tZ) tZ
| Shr : op (Prod tZ tZ) tZ
| And : op (Prod tZ tZ) tZ.
Definition interp_op src dst (f : op src dst) : interp_flat_type_gen interp_base_type src -> interp_flat_type_gen interp_base_type dst
  := match f with
     | Add => fun xy => fst xy + snd xy
     | Mul => fun xy => fst xy * snd xy
     | Sub => fun xy => fst xy - snd xy
     | Shl => fun xy => fst xy << snd xy
     | Shr => fun xy => fst xy >> snd xy
     | And => fun xy => Z.land (fst xy) (snd xy)
     end%Z.

Ltac base_reify_op op op_head ::=
     lazymatch op_head with
     | @Z.add => constr:(reify_op op op_head 2 Add)
     | @Z.mul => constr:(reify_op op op_head 2 Mul)
     | @Z.sub => constr:(reify_op op op_head 2 Sub)
     | @Z.shiftl => constr:(reify_op op op_head 2 Shl)
     | @Z.shiftr => constr:(reify_op op op_head 2 Shr)
     | @Z.land => constr:(reify_op op op_head 2 And)
     end.
Ltac base_reify_type T ::=
     match T with
     | Z => TZ
     end.

Require Import Crypto.Reflection.Linearize.
Ltac Reify' e := Reify.Reify' base_type (interp_base_type _) op e.
Ltac Reify e :=
  let v := Reify.Reify base_type (interp_base_type) op e in
  constr:((*Inline _*) ((*CSE _*) ((*InlineConst*) (Linearize v)))).
Ltac Reify_rhs := Reify.Reify_rhs base_type (interp_base_type) op interp_op.
Import ReifyDebugNotations.

Local Transparent Let_In.
Definition max := 2^64.
Record BoundsOnZ := { lower : Z ; v : Z ; upper : Z }.
Definition boundedZ := option { b : BoundsOnZ | 0 <= lower b /\ lower b <= v b <= upper b /\ upper b < max }.

Definition bounded_interp_base_type (v : base_type) : Type :=
  match v with
  | TZ => boundedZ
  end.
Axiom admit : forall {T}, T.
Definition bounded_add (x y : boundedZ) : boundedZ.
Proof.
  refine match x, y with
         | Some (exist x' xp), Some (exist y' yp) => _
         | _, _ => None
         end.
  destruct (upper x' + upper y' <? max) eqn:H.
  { apply Some;
      exists {| lower := lower x' + lower y' ; v := v x' + v y' ; upper := upper x' + upper y' |}.
    Z.ltb_to_lt.
    simpl in *; repeat split; try omega. }
  { apply None. }
Defined.
Definition bounded_mul (x y : boundedZ) : boundedZ.
Proof.
  refine match x, y with
         | Some (exist x' xp), Some (exist y' yp) => _
         | _, _ => None
         end.
  destruct (upper x' * upper y' <? max) eqn:H.
  { apply Some;
      exists {| lower := lower x' * lower y' ; v := v x' * v y' ; upper := upper x' * upper y' |}.
    Z.ltb_to_lt.
    simpl in *; nia. }
  { apply None. }
Defined.
Definition bounded_shl (x y : boundedZ) : boundedZ.
Proof.
  refine match x, y with
         | Some (exist x' xp), Some (exist y' yp) => _
         | _, _ => None
         end.
  destruct (upper x' << upper y' <? max) eqn:H.
  { apply Some;
      exists {| lower := lower x' << lower y' ; v := v x' << v y' ; upper := upper x' << upper y' |}.
    Z.ltb_to_lt.
    simpl in *; autorewrite with Zshift_to_pow in *.
    assert (0 <= 2^lower y' /\ 2^lower y' <= 2^v y' <= 2^upper y') by auto with zarith.
    nia. }
  { apply None. }
Defined.
Definition bounded_shr (x y : boundedZ) : boundedZ.
Proof.
  refine match x, y with
         | Some (exist x' xp), Some (exist y' yp) => Some _
         | _, _ => None
         end.
  exists {| lower := lower x' >> upper y' ; v := v x' >> v y' ; upper := upper x' >> lower y' |}.
  simpl in *; autorewrite with Zshift_to_pow in *.
  assert (0 <= 2^lower y' /\ 2^lower y' <= 2^v y' <= 2^upper y') by auto with zarith.
  assert (0 < 2^upper y') by zero_bounds.
  assert (0 < 2^lower y') by zero_bounds.
  assert (0 < 2^v y') by zero_bounds.
  repeat split; auto with zarith.
  { transitivity (v x' / 2^upper y').
    { apply Z_div_le; omega. }
    { apply Z.div_le_compat_l; omega. } }
  { transitivity (upper x' / 2^v y').
    { apply Z_div_le; omega. }
    { apply Z.div_le_compat_l; omega. } }
  { apply Zdiv_lt_upper_bound; nia. }
Defined.
Definition bounded_and (x y : boundedZ) : boundedZ.
Proof.
  refine match x, y with
         | Some (exist x' xp), Some (exist y' yp) => Some _
         | _, _ => None
         end.
  exists {| lower := 0 ; v := v x' &' v y' ; upper := Z.min (upper x') (upper y') |}.
  simpl in *.
  repeat split; try auto with zarith.
  { apply Z.land_nonneg; omega. }
  { Hint Resolve Z.land_upper_bound_l Z.land_upper_bound_r : zarith.
    apply Z.min_case_strong; intros; etransitivity; eauto with zarith. }
  { apply Z.min_case_strong; auto with zarith. }
Defined.
Definition bounded_sub (x y : boundedZ) : boundedZ.
Proof.
  refine match x, y with
         | Some (exist x' xp), Some (exist y' yp) => _
         | _, _ => None
         end.
  destruct (lower x' - upper y' <? 0) eqn:H.
  { exact None. }
  { apply Some.
    exists {| lower := lower x' - upper y' ; v := v x' - v y' ; upper := upper x' - lower y' |}.
    Z.ltb_to_lt.
    simpl in *.
    (** TODO: Debug: report anomaly on omega rather than lia *)
    lia. }
Defined.
Definition bounded_interp_op src dst (f : op src dst) : interp_flat_type_gen bounded_interp_base_type src -> interp_flat_type_gen bounded_interp_base_type dst
  := match f with
     | Add => fun xy => bounded_add (fst xy) (snd xy)
     | Mul => fun xy => bounded_mul (fst xy) (snd xy)
     | Sub => fun xy => bounded_sub (fst xy) (snd xy)
     | Shl => fun xy => bounded_shl (fst xy) (snd xy)
     | Shr => fun xy => bounded_shr (fst xy) (snd xy)
     | And => fun xy => bounded_and (fst xy) (snd xy)
     end%Z.
Require Import Crypto.Reflection.MapInterp.
Definition f t : interp_base_type t -> bounded_interp_base_type t.
Proof.
  refine match t return interp_base_type t -> bounded_interp_base_type t with
         | TZ => fun x => _
         end.
  destruct (x <? 0) eqn:H.
  { apply None. }
  { destruct (x <? max) eqn:H'.
    { refine (Some (exist _ {| lower := x ; v := x ; upper := x |} _)).
      Z.ltb_to_lt.
      simpl in *; omega. }
    { apply None. } }
Defined.
Print mul.
Inductive Zv {A B} := TTT (e : A) (p : B).
Notation "2^ e + p" := (TTT e p) (at level 10, format "2^ e  +  p").

Definition rexprm : Syntax.Expr base_type interp_base_type op
        (TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ -> TZ -> TZ -> TZ -> TZ -> TZ -> tZ * tZ * tZ * tZ * tZ * tZ * tZ * tZ * tZ * tZ)%ctype.
Proof.
  let v := (eval cbv beta iota delta [Let_In mul fe25519] in (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 => mul (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9)  (y0, y1, y2, y3, y4, y5, y6, y7, y8, y9))) in
  let r := Reify v in
  let r := (eval vm_compute in r) in
  exact r.
Defined.

Definition mulh :=
fun f g : fe25519 =>
let (f0, g0) := f in
let (f1, g1) := f0 in
let (f2, g2) := f1 in
let (f3, g3) := f2 in
let (f4, g4) := f3 in
let (f5, g5) := f4 in
let (f6, g6) := f5 in
let (f7, g7) := f6 in
let (f8, g8) := f7 in
let (f9, g9) := g in
let (f10, g10) := f9 in
let (f11, g11) := f10 in
let (f12, g12) := f11 in
let (f13, g13) := f12 in
let (f14, g14) := f13 in
let (f15, g15) := f14 in
let (f16, g16) := f15 in
let '(f17, g17) := f16 in
dlet z := g0 * g9 +
          19 *
          (f8 * (g10 * 2) +
           (g8 * g11 +
            (g7 * (g12 * 2) +
             (g6 * g13 +
              (g5 * (g14 * 2) + (g4 * g15 + (g3 * (g16 * 2) + (g2 * g17 + g1 * (f17 * 2))))))))) in
      dlet z0 := z >> 26 +
           (g1 * g9 + g0 * g10 +
            19 *
            (f8 * g11 +
             (g8 * g12 +
              (g7 * g13 + (g6 * g14 + (g5 * g15 + (g4 * g16 + (g3 * g17 + g2 * f17)))))))) in
dlet z1 := z0 >> 25 +
           (g2 * g9 + (g1 * (g10 * 2) + g0 * g11) +
            19 *
            (f8 * (g12 * 2) +
             (g8 * g13 +
              (g7 * (g14 * 2) + (g6 * g15 + (g5 * (g16 * 2) + (g4 * g17 + g3 * (f17 * 2)))))))) in
dlet z2 := z1 >> 26 +
           (g3 * g9 + (g2 * g10 + (g1 * g11 + g0 * g12)) +
            19 * (f8 * g13 + (g8 * g14 + (g7 * g15 + (g6 * g16 + (g5 * g17 + g4 * f17)))))) in
dlet z3 := z2 >> 25 +
           (g4 * g9 + (g3 * (g10 * 2) + (g2 * g11 + (g1 * (g12 * 2) + g0 * g13))) +
            19 * (f8 * (g14 * 2) + (g8 * g15 + (g7 * (g16 * 2) + (g6 * g17 + g5 * (f17 * 2)))))) in
dlet z4 := z3 >> 26 +
           (g5 * g9 + (g4 * g10 + (g3 * g11 + (g2 * g12 + (g1 * g13 + g0 * g14)))) +
            19 * (f8 * g15 + (g8 * g16 + (g7 * g17 + g6 * f17)))) in
dlet z5 := z4 >> 25 +
           (g6 * g9 +
            (g5 * (g10 * 2) +
             (g4 * g11 + (g3 * (g12 * 2) + (g2 * g13 + (g1 * (g14 * 2) + g0 * g15))))) +
            19 * (f8 * (g16 * 2) + (g8 * g17 + g7 * (f17 * 2)))) in
dlet z6 := z5 >> 26 +
           (g7 * g9 +
            (g6 * g10 + (g5 * g11 + (g4 * g12 + (g3 * g13 + (g2 * g14 + (g1 * g15 + g0 * g16)))))) +
            19 * (f8 * g17 + g8 * f17)) in
dlet z7 := z6 >> 25 +
           (g8 * g9 +
            (g7 * (g10 * 2) +
             (g6 * g11 +
              (g5 * (g12 * 2) +
               (g4 * g13 + (g3 * (g14 * 2) + (g2 * g15 + (g1 * (g16 * 2) + g0 * g17))))))) +
            19 * (f8 * (f17 * 2))) in
dlet z8 := z7 >> 26 +
           (f8 * g9 +
            (g8 * g10 +
             (g7 * g11 +
              (g6 * g12 +
               (g5 * g13 + (g4 * g14 + (g3 * g15 + (g2 * g16 + (g1 * g17 + g0 * f17))))))))) in
dlet z9 := 19 * z8 >> 25 + (z &' 67108863) in
dlet z10 := z9 >> 26 + (z0 &' 33554431) in
(z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z8 &' 33554431, z7 &' 67108863, z6 &' 33554431, z5 &' 67108863, z4 &' 33554431,
z3 &' 67108863, z2 &' 33554431, z10 >> 25 + (z1 &' 67108863), z10 &' 33554431,
z9 &' 67108863).

Definition rexprhm : Syntax.Expr base_type interp_base_type op
        (TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ -> TZ -> TZ -> TZ -> TZ -> TZ -> tZ * tZ * tZ * tZ * tZ * tZ * tZ * tZ * tZ * tZ * tZ * tZ * tZ * tZ * tZ * tZ * tZ * tZ * tZ * tZ * tZ)%ctype.
Proof.
  let v := (eval cbv beta iota delta [Let_In mulh fe25519] in (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 => mulh (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9)  (y0, y1, y2, y3, y4, y5, y6, y7, y8, y9))) in
  let r := Reify v in
  let r := (eval vm_compute in r) in
  exact r.
Defined.

Definition compute_boundshm (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Z * Z)
  := fun vx0 vx1 vx2 vx3 vx4 vx5 vx6 vx7 vx8 vx9 vy0 vy1 vy2 vy3 vy4 vy5 vy6 vy7 vy8 vy9
         pfx0 pfx1 pfx2 pfx3 pfx4 pfx5 pfx6 pfx7 pfx8 pfx9 pfy0 pfy1 pfy2 pfy3 pfy4 pfy5 pfy6 pfy7 pfy8 pfy9
     =>
       let x0 : boundedZ := Some (exist _ {| lower := fst x0 ; v := vx0 ; upper := snd x0 |} pfx0) in
       let x1 : boundedZ := Some (exist _ {| lower := fst x1 ; v := vx1 ; upper := snd x1 |} pfx1) in
       let x2 : boundedZ := Some (exist _ {| lower := fst x2 ; v := vx2 ; upper := snd x2 |} pfx2) in
       let x3 : boundedZ := Some (exist _ {| lower := fst x3 ; v := vx3 ; upper := snd x3 |} pfx3) in
       let x4 : boundedZ := Some (exist _ {| lower := fst x4 ; v := vx4 ; upper := snd x4 |} pfx4) in
       let x5 : boundedZ := Some (exist _ {| lower := fst x5 ; v := vx5 ; upper := snd x5 |} pfx5) in
       let x6 : boundedZ := Some (exist _ {| lower := fst x6 ; v := vx6 ; upper := snd x6 |} pfx6) in
       let x7 : boundedZ := Some (exist _ {| lower := fst x7 ; v := vx7 ; upper := snd x7 |} pfx7) in
       let x8 : boundedZ := Some (exist _ {| lower := fst x8 ; v := vx8 ; upper := snd x8 |} pfx8) in
       let x9 : boundedZ := Some (exist _ {| lower := fst x9 ; v := vx9 ; upper := snd x9 |} pfx9) in
       let y0 : boundedZ := Some (exist _ {| lower := fst y0 ; v := vy0 ; upper := snd y0 |} pfy0) in
       let y1 : boundedZ := Some (exist _ {| lower := fst y1 ; v := vy1 ; upper := snd y1 |} pfy1) in
       let y2 : boundedZ := Some (exist _ {| lower := fst y2 ; v := vy2 ; upper := snd y2 |} pfy2) in
       let y3 : boundedZ := Some (exist _ {| lower := fst y3 ; v := vy3 ; upper := snd y3 |} pfy3) in
       let y4 : boundedZ := Some (exist _ {| lower := fst y4 ; v := vy4 ; upper := snd y4 |} pfy4) in
       let y5 : boundedZ := Some (exist _ {| lower := fst y5 ; v := vy5 ; upper := snd y5 |} pfy5) in
       let y6 : boundedZ := Some (exist _ {| lower := fst y6 ; v := vy6 ; upper := snd y6 |} pfy6) in
       let y7 : boundedZ := Some (exist _ {| lower := fst y7 ; v := vy7 ; upper := snd y7 |} pfy7) in
       let y8 : boundedZ := Some (exist _ {| lower := fst y8 ; v := vy8 ; upper := snd y8 |} pfy8) in
       let y9 : boundedZ := Some (exist _ {| lower := fst y9 ; v := vy9 ; upper := snd y9 |} pfy9) in
       match Syntax.Interp bounded_interp_op (@MapInterp _ interp_base_type bounded_interp_base_type op f _ rexprhm) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 with
       | (Some (exist b0 _), Some (exist b1 _), Some (exist b2 _), Some (exist b3 _), Some (exist b4 _), Some (exist b5 _), Some (exist b6 _), Some (exist b7 _), Some (exist b8 _), Some (exist b9 _), Some (exist b10 _), Some (exist b11 _), Some (exist b12 _), Some (exist b13 _), Some (exist b14 _), Some (exist b15 _), Some (exist b16 _), Some (exist b17 _), Some (exist b18 _), Some (exist b19 _), Some (exist b20 _))
         => let f b := (lower b, let u := upper b in let u' := Z.log2 u in TTT u' (let u := u - 2^u' in let u' := Z.log2 u in TTT u' (let u := u - 2^u' in u))) in
            Some (f b0, f b1, f b2, f b3, f b4, f b5, f b6, f b7, f b8, f b9, f b10, f b11, f b12, f b13, f b14, f b15, f b16, f b17, f b18, f b19, f b20)
       | _ => None
       end.
Notation be exp := (0, 2^exp + 2^exp / 10)%Z.
(*Goal True.
  pose mul.
  cbv [mul] in f0.
Compute compute_boundsm (be 26) (be 25) (be 26) (be 25) (be 26) (be 25) (be 26) (be 25) (be 26) (be 25) (be 26) (be 25) (be 26) (be 25) (be 26) (be 25) (be 26) (be 25) (be 26) (be 25).




*)

Definition rexprs : Syntax.Expr base_type interp_base_type op
        (TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ -> TZ -> TZ -> TZ -> TZ -> TZ -> tZ * tZ * tZ * tZ * tZ * tZ * tZ * tZ * tZ * tZ)%ctype.
Proof.
  let v := (eval cbv beta iota delta [Let_In sub fe25519] in (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 => sub (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9)  (y0, y1, y2, y3, y4, y5, y6, y7, y8, y9))) in
  let r := Reify v in
  let r := (eval vm_compute in r) in
  exact r.
Defined.

Definition rexpro : Syntax.Expr base_type interp_base_type op
        (TZ ->
         TZ ->
         TZ ->
         TZ ->
         TZ -> TZ -> TZ -> TZ -> TZ -> TZ -> tZ * tZ * tZ * tZ * tZ * tZ * tZ * tZ * tZ * tZ)%ctype.
Proof.
  let v := (eval cbv beta iota delta [Let_In opp fe25519] in (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 => opp (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9))) in
  let r := Reify v in
  let r := (eval vm_compute in r) in
  exact r.
Defined.

Definition compute_boundsm (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Z * Z)
  := fun vx0 vx1 vx2 vx3 vx4 vx5 vx6 vx7 vx8 vx9 vy0 vy1 vy2 vy3 vy4 vy5 vy6 vy7 vy8 vy9
         pfx0 pfx1 pfx2 pfx3 pfx4 pfx5 pfx6 pfx7 pfx8 pfx9 pfy0 pfy1 pfy2 pfy3 pfy4 pfy5 pfy6 pfy7 pfy8 pfy9
     =>
       let x0 : boundedZ := Some (exist _ {| lower := fst x0 ; v := vx0 ; upper := snd x0 |} pfx0) in
       let x1 : boundedZ := Some (exist _ {| lower := fst x1 ; v := vx1 ; upper := snd x1 |} pfx1) in
       let x2 : boundedZ := Some (exist _ {| lower := fst x2 ; v := vx2 ; upper := snd x2 |} pfx2) in
       let x3 : boundedZ := Some (exist _ {| lower := fst x3 ; v := vx3 ; upper := snd x3 |} pfx3) in
       let x4 : boundedZ := Some (exist _ {| lower := fst x4 ; v := vx4 ; upper := snd x4 |} pfx4) in
       let x5 : boundedZ := Some (exist _ {| lower := fst x5 ; v := vx5 ; upper := snd x5 |} pfx5) in
       let x6 : boundedZ := Some (exist _ {| lower := fst x6 ; v := vx6 ; upper := snd x6 |} pfx6) in
       let x7 : boundedZ := Some (exist _ {| lower := fst x7 ; v := vx7 ; upper := snd x7 |} pfx7) in
       let x8 : boundedZ := Some (exist _ {| lower := fst x8 ; v := vx8 ; upper := snd x8 |} pfx8) in
       let x9 : boundedZ := Some (exist _ {| lower := fst x9 ; v := vx9 ; upper := snd x9 |} pfx9) in
       let y0 : boundedZ := Some (exist _ {| lower := fst y0 ; v := vy0 ; upper := snd y0 |} pfy0) in
       let y1 : boundedZ := Some (exist _ {| lower := fst y1 ; v := vy1 ; upper := snd y1 |} pfy1) in
       let y2 : boundedZ := Some (exist _ {| lower := fst y2 ; v := vy2 ; upper := snd y2 |} pfy2) in
       let y3 : boundedZ := Some (exist _ {| lower := fst y3 ; v := vy3 ; upper := snd y3 |} pfy3) in
       let y4 : boundedZ := Some (exist _ {| lower := fst y4 ; v := vy4 ; upper := snd y4 |} pfy4) in
       let y5 : boundedZ := Some (exist _ {| lower := fst y5 ; v := vy5 ; upper := snd y5 |} pfy5) in
       let y6 : boundedZ := Some (exist _ {| lower := fst y6 ; v := vy6 ; upper := snd y6 |} pfy6) in
       let y7 : boundedZ := Some (exist _ {| lower := fst y7 ; v := vy7 ; upper := snd y7 |} pfy7) in
       let y8 : boundedZ := Some (exist _ {| lower := fst y8 ; v := vy8 ; upper := snd y8 |} pfy8) in
       let y9 : boundedZ := Some (exist _ {| lower := fst y9 ; v := vy9 ; upper := snd y9 |} pfy9) in
       match Syntax.Interp bounded_interp_op (@MapInterp _ interp_base_type bounded_interp_base_type op f _ rexprm) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 with
       | (Some (exist b0 _), Some (exist b1 _), Some (exist b2 _), Some (exist b3 _), Some (exist b4 _), Some (exist b5 _), Some (exist b6 _), Some (exist b7 _), Some (exist b8 _), Some (exist b9 _))
         => let f b := (lower b, let u := upper b in let u' := Z.log2 u in TTT u' (let u := u - 2^u' in let u' := Z.log2 u in TTT u' (let u := u - 2^u' in u))) in
            Some (f b0, f b1, f b2, f b3, f b4, f b5, f b6, f b7, f b8, f b9)
       | _ => None
       end.
Definition compute_boundss (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Z * Z)
  := fun vx0 vx1 vx2 vx3 vx4 vx5 vx6 vx7 vx8 vx9 vy0 vy1 vy2 vy3 vy4 vy5 vy6 vy7 vy8 vy9
         pfx0 pfx1 pfx2 pfx3 pfx4 pfx5 pfx6 pfx7 pfx8 pfx9 pfy0 pfy1 pfy2 pfy3 pfy4 pfy5 pfy6 pfy7 pfy8 pfy9
     =>
       let x0 : boundedZ := Some (exist _ {| lower := fst x0 ; v := vx0 ; upper := snd x0 |} pfx0) in
       let x1 : boundedZ := Some (exist _ {| lower := fst x1 ; v := vx1 ; upper := snd x1 |} pfx1) in
       let x2 : boundedZ := Some (exist _ {| lower := fst x2 ; v := vx2 ; upper := snd x2 |} pfx2) in
       let x3 : boundedZ := Some (exist _ {| lower := fst x3 ; v := vx3 ; upper := snd x3 |} pfx3) in
       let x4 : boundedZ := Some (exist _ {| lower := fst x4 ; v := vx4 ; upper := snd x4 |} pfx4) in
       let x5 : boundedZ := Some (exist _ {| lower := fst x5 ; v := vx5 ; upper := snd x5 |} pfx5) in
       let x6 : boundedZ := Some (exist _ {| lower := fst x6 ; v := vx6 ; upper := snd x6 |} pfx6) in
       let x7 : boundedZ := Some (exist _ {| lower := fst x7 ; v := vx7 ; upper := snd x7 |} pfx7) in
       let x8 : boundedZ := Some (exist _ {| lower := fst x8 ; v := vx8 ; upper := snd x8 |} pfx8) in
       let x9 : boundedZ := Some (exist _ {| lower := fst x9 ; v := vx9 ; upper := snd x9 |} pfx9) in
       let y0 : boundedZ := Some (exist _ {| lower := fst y0 ; v := vy0 ; upper := snd y0 |} pfy0) in
       let y1 : boundedZ := Some (exist _ {| lower := fst y1 ; v := vy1 ; upper := snd y1 |} pfy1) in
       let y2 : boundedZ := Some (exist _ {| lower := fst y2 ; v := vy2 ; upper := snd y2 |} pfy2) in
       let y3 : boundedZ := Some (exist _ {| lower := fst y3 ; v := vy3 ; upper := snd y3 |} pfy3) in
       let y4 : boundedZ := Some (exist _ {| lower := fst y4 ; v := vy4 ; upper := snd y4 |} pfy4) in
       let y5 : boundedZ := Some (exist _ {| lower := fst y5 ; v := vy5 ; upper := snd y5 |} pfy5) in
       let y6 : boundedZ := Some (exist _ {| lower := fst y6 ; v := vy6 ; upper := snd y6 |} pfy6) in
       let y7 : boundedZ := Some (exist _ {| lower := fst y7 ; v := vy7 ; upper := snd y7 |} pfy7) in
       let y8 : boundedZ := Some (exist _ {| lower := fst y8 ; v := vy8 ; upper := snd y8 |} pfy8) in
       let y9 : boundedZ := Some (exist _ {| lower := fst y9 ; v := vy9 ; upper := snd y9 |} pfy9) in
       match Syntax.Interp bounded_interp_op (@MapInterp _ interp_base_type bounded_interp_base_type op f _ rexprs) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 with
       | (Some (exist b0 _), Some (exist b1 _), Some (exist b2 _), Some (exist b3 _), Some (exist b4 _), Some (exist b5 _), Some (exist b6 _), Some (exist b7 _), Some (exist b8 _), Some (exist b9 _))
         => let f b := (lower b, let u := upper b in let u' := Z.log2 u in TTT u' (let u := u - 2^u' in let u' := Z.log2 u in TTT u' (let u := u - 2^u' in u))) in
            Some (f b0, f b1, f b2, f b3, f b4, f b5, f b6, f b7, f b8, f b9)
       | _ => None
       end.
Definition compute_boundso (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Z * Z)
  := fun vx0 vx1 vx2 vx3 vx4 vx5 vx6 vx7 vx8 vx9
         pfx0 pfx1 pfx2 pfx3 pfx4 pfx5 pfx6 pfx7 pfx8 pfx9
     =>
       let x0 : boundedZ := Some (exist _ {| lower := fst x0 ; v := vx0 ; upper := snd x0 |} pfx0) in
       let x1 : boundedZ := Some (exist _ {| lower := fst x1 ; v := vx1 ; upper := snd x1 |} pfx1) in
       let x2 : boundedZ := Some (exist _ {| lower := fst x2 ; v := vx2 ; upper := snd x2 |} pfx2) in
       let x3 : boundedZ := Some (exist _ {| lower := fst x3 ; v := vx3 ; upper := snd x3 |} pfx3) in
       let x4 : boundedZ := Some (exist _ {| lower := fst x4 ; v := vx4 ; upper := snd x4 |} pfx4) in
       let x5 : boundedZ := Some (exist _ {| lower := fst x5 ; v := vx5 ; upper := snd x5 |} pfx5) in
       let x6 : boundedZ := Some (exist _ {| lower := fst x6 ; v := vx6 ; upper := snd x6 |} pfx6) in
       let x7 : boundedZ := Some (exist _ {| lower := fst x7 ; v := vx7 ; upper := snd x7 |} pfx7) in
       let x8 : boundedZ := Some (exist _ {| lower := fst x8 ; v := vx8 ; upper := snd x8 |} pfx8) in
       let x9 : boundedZ := Some (exist _ {| lower := fst x9 ; v := vx9 ; upper := snd x9 |} pfx9) in
       match Syntax.Interp bounded_interp_op (@MapInterp _ interp_base_type bounded_interp_base_type op f _ rexpro) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 with
       | (Some (exist b0 _), Some (exist b1 _), Some (exist b2 _), Some (exist b3 _), Some (exist b4 _), Some (exist b5 _), Some (exist b6 _), Some (exist b7 _), Some (exist b8 _), Some (exist b9 _))
         => let f b := (lower b, let u := upper b in let u' := Z.log2 u in TTT u' (let u := u - 2^u' in let u' := Z.log2 u in TTT u' (let u := u - 2^u' in u))) in
            Some (f b0, f b1, f b2, f b3, f b4, f b5, f b6, f b7, f b8, f b9)
       | _ => None
       end.
Definition compute_uboundsm (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : Z * Z)
  := fun vx0 vx1 vx2 vx3 vx4 vx5 vx6 vx7 vx8 vx9 vy0 vy1 vy2 vy3 vy4 vy5 vy6 vy7 vy8 vy9
         pfx0 pfx1 pfx2 pfx3 pfx4 pfx5 pfx6 pfx7 pfx8 pfx9 pfy0 pfy1 pfy2 pfy3 pfy4 pfy5 pfy6 pfy7 pfy8 pfy9
     =>
       let x0 : boundedZ := Some (exist _ {| lower := fst x0 ; v := vx0 ; upper := snd x0 |} pfx0) in
       let x1 : boundedZ := Some (exist _ {| lower := fst x1 ; v := vx1 ; upper := snd x1 |} pfx1) in
       let x2 : boundedZ := Some (exist _ {| lower := fst x2 ; v := vx2 ; upper := snd x2 |} pfx2) in
       let x3 : boundedZ := Some (exist _ {| lower := fst x3 ; v := vx3 ; upper := snd x3 |} pfx3) in
       let x4 : boundedZ := Some (exist _ {| lower := fst x4 ; v := vx4 ; upper := snd x4 |} pfx4) in
       let x5 : boundedZ := Some (exist _ {| lower := fst x5 ; v := vx5 ; upper := snd x5 |} pfx5) in
       let x6 : boundedZ := Some (exist _ {| lower := fst x6 ; v := vx6 ; upper := snd x6 |} pfx6) in
       let x7 : boundedZ := Some (exist _ {| lower := fst x7 ; v := vx7 ; upper := snd x7 |} pfx7) in
       let x8 : boundedZ := Some (exist _ {| lower := fst x8 ; v := vx8 ; upper := snd x8 |} pfx8) in
       let x9 : boundedZ := Some (exist _ {| lower := fst x9 ; v := vx9 ; upper := snd x9 |} pfx9) in
       let y0 : boundedZ := Some (exist _ {| lower := fst y0 ; v := vy0 ; upper := snd y0 |} pfy0) in
       let y1 : boundedZ := Some (exist _ {| lower := fst y1 ; v := vy1 ; upper := snd y1 |} pfy1) in
       let y2 : boundedZ := Some (exist _ {| lower := fst y2 ; v := vy2 ; upper := snd y2 |} pfy2) in
       let y3 : boundedZ := Some (exist _ {| lower := fst y3 ; v := vy3 ; upper := snd y3 |} pfy3) in
       let y4 : boundedZ := Some (exist _ {| lower := fst y4 ; v := vy4 ; upper := snd y4 |} pfy4) in
       let y5 : boundedZ := Some (exist _ {| lower := fst y5 ; v := vy5 ; upper := snd y5 |} pfy5) in
       let y6 : boundedZ := Some (exist _ {| lower := fst y6 ; v := vy6 ; upper := snd y6 |} pfy6) in
       let y7 : boundedZ := Some (exist _ {| lower := fst y7 ; v := vy7 ; upper := snd y7 |} pfy7) in
       let y8 : boundedZ := Some (exist _ {| lower := fst y8 ; v := vy8 ; upper := snd y8 |} pfy8) in
       let y9 : boundedZ := Some (exist _ {| lower := fst y9 ; v := vy9 ; upper := snd y9 |} pfy9) in
       match Syntax.Interp bounded_interp_op (@MapInterp _ interp_base_type bounded_interp_base_type op f _ rexprm) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 with
       | (Some (exist b0 _), Some (exist b1 _), Some (exist b2 _), Some (exist b3 _), Some (exist b4 _), Some (exist b5 _), Some (exist b6 _), Some (exist b7 _), Some (exist b8 _), Some (exist b9 _))
         => let f b := upper b in
            Some (f b0, f b1, f b2, f b3, f b4, f b5, f b6, f b7, f b8, f b9)
       | _ => None
       end.
Compute (2^26 - 67108862).
Print sub.
Compute (2^26 - (2^25 + (2^24 + 16777215))).
Compute (2^25 - (2^24 + (2^23 + 8388607))).
Notation be' exp := (0, 2^(exp+2) + 2^(exp) + 2^(exp-1) + 2^(exp-3) + 2^(exp-4) + 2^(exp-5) + 2^(exp-6) + 2^(exp-10) + 2^(exp-12) + 2^(exp-13) + 2^(exp-14) + 2^(exp-15) + 2^(exp-17) + 2^(exp-23) + 2^(exp-24))%Z.
Compute compute_boundsm (be' 25) (be' 26) (be' 25) (be' 26) (be' 25) (be' 26) (be' 25) (be' 26) (be' 25) (be' 26) (be' 25) (be' 26) (be' 25) (be' 26) (be' 25) (be' 26) (be' 25) (be' 26) (be' 25) (be' 26) .
Compute compute_boundss (be 25) (be 26) (be 25) (be 26) (be 25) (be 26) (be 25) (be 26) (be 25) (be 26) (be 25) (be 26) (be 25) (be 26) (be 25) (be 26) (be 25) (be 26) (be 25) (be 26) .
Compute compute_boundso (be 25) (be 26) (be 25) (be 26) (be 25) (be 26) (be 25) (be 26) (be 25) (be 26).
