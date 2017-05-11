(** * Hint Databases with lemmas about ℤ from the standard library *)
Require Import Coq.micromega.Psatz Coq.omega.Omega.
Require Import Coq.ZArith.ZArith.

Hint Extern 1 => lia : lia.
Hint Extern 1 => lra : lra.
Hint Extern 1 => nia : nia.
Hint Extern 1 => omega : omega.
Hint Resolve Z.log2_nonneg Z.log2_up_nonneg Z.div_small Z.mod_small Z.pow_neg_r Z.pow_0_l Z.pow_pos_nonneg Z.lt_le_incl Z.pow_nonzero Z.div_le_upper_bound Z_div_exact_full_2 Z.div_same Z.div_lt_upper_bound Z.div_le_lower_bound Zplus_minus Zplus_gt_compat_l Zplus_gt_compat_r Zmult_gt_compat_l Zmult_gt_compat_r Z.pow_lt_mono_r Z.pow_lt_mono_l Z.pow_lt_mono Z.mul_lt_mono_nonneg Z.div_lt_upper_bound Z.div_pos Zmult_lt_compat_r Z.pow_le_mono_r Z.pow_le_mono_l Z.div_lt Z.div_le_compat_l Z.div_le_mono Z.max_le_compat Z.min_le_compat Z.log2_up_le_mono Z.pow_nonneg : zarith.
Hint Resolve (fun a b H => proj1 (Z.mod_pos_bound a b H)) (fun a b H => proj2 (Z.mod_pos_bound a b H)) (fun a b pf => proj1 (Z.pow_gt_1 a b pf)) : zarith.
Hint Resolve (fun n m => proj1 (Z.opp_le_mono n m)) : zarith.
Hint Resolve (fun n m => proj1 (Z.pred_le_mono n m)) : zarith.
Hint Resolve (fun a b => proj2 (Z.lor_nonneg a b)) : zarith.

Ltac zutil_arith := solve [ omega | lia | auto with nocore ].
Ltac zutil_arith_more_inequalities := solve [ zutil_arith | auto with zarith ].

(** Only hints that are always safe to apply (i.e., reversible), and
    which can reasonably be said to "simplify" the goal, should go in
    this database. *)
Create HintDb zsimplify discriminated.
(** Only hints that are always safe to apply, and "simplify" the goal,
    and don't require any side conditions, should go in this
    database. *)
Create HintDb zsimplify_fast discriminated.
(** Hints which turn [Z] operations on concrete positives into the
    corresponding operation on [Pos]. *)
Create HintDb zsimplify_Z_to_pos discriminated.
(** Only hints with no side conditions that strip constants, and
    nothing else. *)
Create HintDb zsimplify_const discriminated.
(** We create separate databases for two directions of transformations
      involving [Z.log2]; combining them leads to loops. *)
(* for hints that take in hypotheses of type [log2 _], and spit out conclusions of type [_ ^ _] *)
Create HintDb hyp_log2 discriminated.
(* for hints that take in hypotheses of type [_ ^ _], and spit out conclusions of type [log2 _] *)
Create HintDb concl_log2 discriminated.
Hint Resolve (fun a b H => proj1 (Z.log2_lt_pow2 a b H)) (fun a b H => proj1 (Z.log2_le_pow2 a b H)) : concl_log2.
Hint Resolve (fun a b H => proj2 (Z.log2_lt_pow2 a b H)) (fun a b H => proj2 (Z.log2_le_pow2 a b H)) : hyp_log2.
Hint Rewrite Z.div_1_r Z.mul_1_r Z.mul_1_l Z.sub_diag Z.mul_0_r Z.mul_0_l Z.add_0_l Z.add_0_r Z.opp_involutive Z.sub_0_r Z_mod_same_full Z.sub_simpl_r Z.sub_simpl_l Z.add_opp_diag_r Z.add_opp_diag_l Zmod_0_l Z.add_simpl_r Z.add_simpl_l Z.opp_0 Zmod_0_r Zmod_mod Z.mul_succ_l Z.mul_succ_r Z.shiftr_0_r Z.shiftr_0_l Z.mod_1_r Zmod_0_l Zmod_0_r Z.shiftl_0_r Z.shiftl_0_l Z.shiftr_0_r Z.shiftr_0_l Z.sub_diag : zsimplify_fast.

Hint Rewrite Z.div_1_r Z.mul_1_r Z.mul_1_l Z.sub_diag Z.mul_0_r Z.mul_0_l Z.add_0_l Z.add_0_r Z.opp_involutive Z.sub_0_r Z_mod_same_full Z.sub_simpl_r Z.sub_simpl_l Z.add_opp_diag_r Z.add_opp_diag_l Zmod_0_l Z.add_simpl_r Z.add_simpl_l Z.opp_0 Zmod_0_r Zmod_mod Z.mul_succ_l Z.mul_succ_r Z.shiftr_0_r Z.shiftr_0_l Z.mod_1_r Zmod_0_l Zmod_0_r Z.shiftl_0_r Z.shiftl_0_l Z.shiftr_0_r Z.shiftr_0_l Zplus_minus Z.add_diag Z.abs_0 Z.sgn_0 Nat2Z.inj_0 Z2Nat.inj_0 : zsimplify.
Hint Rewrite Z.div_mul Z.div_1_l Z.div_same Z.mod_same Z.div_small Z.mod_small Z.div_add Z.div_add_l Z.mod_add Z.div_0_l Z.mod_mod Z.mod_small Z_mod_zero_opp_full Z.mod_1_l using zutil_arith : zsimplify.
Hint Rewrite <- Z.opp_eq_mul_m1 Z.one_succ Z.two_succ : zsimplify.
Hint Rewrite <- Z.div_mod using zutil_arith : zsimplify.
Hint Rewrite (fun x y => proj2 (Z.eqb_neq x y)) using assumption : zsimplify.
Hint Rewrite Z.mul_0_l Z.mul_0_r Z.mul_1_l Z.mul_1_r Z.add_0_l Z.add_0_r Z.sub_0_l Z.sub_0_r Zdiv_0_l Zdiv_0_r Zdiv_1_r Zmod_0_l Zmod_0_r Zmod_1_r Z.opp_0 Z.abs_0 Z.sgn_0 Nat2Z.inj_0 Z2Nat.inj_0 : zsimplify_const.

Hint Rewrite <- Z.one_succ Z.two_succ : zsimplify_const.

(** "push" means transform [-f x] to [f (-x)]; "pull" means go the other way *)
Create HintDb push_Zopp discriminated.
Create HintDb pull_Zopp discriminated.
Create HintDb push_Zpow discriminated.
Create HintDb pull_Zpow discriminated.
Create HintDb push_Zmul discriminated.
Create HintDb pull_Zmul discriminated.
Create HintDb push_Zdiv discriminated.
Create HintDb pull_Zdiv discriminated.
Create HintDb push_Zadd discriminated.
Create HintDb pull_Zadd discriminated.
Create HintDb push_Zsub discriminated.
Create HintDb pull_Zsub discriminated.
Create HintDb pull_Zmod discriminated.
Create HintDb push_Zmod discriminated.
Create HintDb pull_Zof_nat discriminated.
Create HintDb push_Zof_nat discriminated.
Create HintDb pull_Zshift discriminated.
Create HintDb push_Zshift discriminated.
Create HintDb pull_Zof_N discriminated.
Create HintDb push_Zof_N discriminated.
Create HintDb pull_Zto_N discriminated.
Create HintDb push_Zto_N discriminated.
Create HintDb Zshift_to_pow discriminated.
Create HintDb Zpow_to_shift discriminated.
Create HintDb pull_Zmax discriminated.
Create HintDb push_Zmax discriminated.
Hint Extern 1 => progress autorewrite with push_Zopp in * : push_Zopp.
Hint Extern 1 => progress autorewrite with pull_Zopp in * : pull_Zopp.
Hint Extern 1 => progress autorewrite with push_Zpow in * : push_Zpow.
Hint Extern 1 => progress autorewrite with pull_Zpow in * : pull_Zpow.
Hint Extern 1 => progress autorewrite with push_Zmul in * : push_Zmul.
Hint Extern 1 => progress autorewrite with pull_Zmul in * : pull_Zmul.
Hint Extern 1 => progress autorewrite with push_Zadd in * : push_Zadd.
Hint Extern 1 => progress autorewrite with pull_Zadd in * : pull_Zadd.
Hint Extern 1 => progress autorewrite with push_Zsub in * : push_Zsub.
Hint Extern 1 => progress autorewrite with pull_Zsub in * : pull_Zsub.
Hint Extern 1 => progress autorewrite with push_Zdiv in * : push_Zmul.
Hint Extern 1 => progress autorewrite with pull_Zdiv in * : pull_Zmul.
Hint Extern 1 => progress autorewrite with pull_Zmod in * : pull_Zmod.
Hint Extern 1 => progress autorewrite with push_Zmod in * : push_Zmod.
Hint Extern 1 => progress autorewrite with pull_Zof_nat in * : pull_Zof_nat.
Hint Extern 1 => progress autorewrite with push_Zof_nat in * : push_Zof_nat.
Hint Extern 1 => progress autorewrite with pull_Zshift in * : pull_Zshift.
Hint Extern 1 => progress autorewrite with push_Zshift in * : push_Zshift.
Hint Extern 1 => progress autorewrite with Zshift_to_pow in * : Zshift_to_pow.
Hint Extern 1 => progress autorewrite with Zpow_to_shift in * : Zpow_to_shift.
Hint Extern 1 => progress autorewrite with pull_Zof_N in * : pull_Zof_N.
Hint Extern 1 => progress autorewrite with push_Zof_N in * : push_Zof_N.
Hint Extern 1 => progress autorewrite with pull_Zto_N in * : pull_Zto_N.
Hint Extern 1 => progress autorewrite with push_Zto_N in * : push_Zto_N.
Hint Extern 1 => progress autorewrite with push_Zmax in * : push_Zmax.
Hint Extern 1 => progress autorewrite with pull_Zmax in * : pull_Zmax.
Hint Rewrite Z.div_opp_l_nz Z.div_opp_l_z using zutil_arith : pull_Zopp.
Hint Rewrite Z.mul_opp_l : pull_Zopp.
Hint Rewrite <- Z.opp_add_distr : pull_Zopp.
Hint Rewrite <- Z.div_opp_l_nz Z.div_opp_l_z using zutil_arith : push_Zopp.
Hint Rewrite <- Z.mul_opp_l : push_Zopp.
Hint Rewrite Z.opp_add_distr : push_Zopp.
Hint Rewrite Z.pow_sub_r Z.pow_div_l Z.pow_twice_r Z.pow_mul_l Z.pow_add_r using zutil_arith : push_Zpow.
Hint Rewrite <- Z.pow_sub_r Z.pow_div_l Z.pow_mul_l Z.pow_add_r Z.pow_twice_r using zutil_arith : pull_Zpow.
Hint Rewrite Z.mul_add_distr_l Z.mul_add_distr_r Z.mul_sub_distr_l Z.mul_sub_distr_r : push_Zmul.
Hint Rewrite <- Z.mul_add_distr_l Z.mul_add_distr_r Z.mul_sub_distr_l Z.mul_sub_distr_r : pull_Zmul.
Hint Rewrite Z.div_div using zutil_arith : pull_Zdiv.
Hint Rewrite <- Z.div_div using zutil_arith : push_Zdiv.
Hint Rewrite <- Z.mul_mod Z.add_mod Zminus_mod using zutil_arith : pull_Zmod.
Hint Rewrite Zminus_mod_idemp_l Zminus_mod_idemp_r : pull_Zmod.
Hint Rewrite Z_mod_nz_opp_full using zutil_arith : push_Zmod.
Hint Rewrite Z_mod_same_full : push_Zmod.
Hint Rewrite Nat2Z.id N2Z.id : zsimplify.
Hint Rewrite Nat2Z.id : push_Zof_nat.
Hint Rewrite N2Z.id : push_Zto_N.
Hint Rewrite N2Z.id : pull_Zof_N.
Hint Rewrite N2Z.inj_pos N2Z.inj_abs_N N2Z.inj_add N2Z.inj_mul N2Z.inj_sub_max N2Z.inj_succ N2Z.inj_pred_max N2Z.inj_min N2Z.inj_max N2Z.inj_div N2Z.inj_quot N2Z.inj_rem N2Z.inj_div2 N2Z.inj_pow N2Z.inj_0 nat_N_Z : push_Zof_N.
Hint Rewrite N2Z.inj_compare N2Z.inj_testbit : pull_Zof_N.
Hint Rewrite <- N2Z.inj_abs_N N2Z.inj_add N2Z.inj_mul N2Z.inj_sub_max N2Z.inj_succ N2Z.inj_pred_max N2Z.inj_min N2Z.inj_max N2Z.inj_div N2Z.inj_quot N2Z.inj_rem N2Z.inj_div2 N2Z.inj_pow : pull_Zof_N.
Hint Rewrite Nat2Z.inj_0 Nat2Z.inj_succ Nat2Z.inj_abs_nat Nat2Z.inj_add Nat2Z.inj_mul Nat2Z.inj_sub_max Nat2Z.inj_pred_max Nat2Z.inj_min Nat2Z.inj_max Zabs2Nat.id_abs Zabs2Nat.id : push_Zof_nat.
Hint Rewrite <- Nat2Z.inj_0 Nat2Z.inj_succ Nat2Z.inj_abs_nat Nat2Z.inj_add Nat2Z.inj_mul Nat2Z.inj_sub_max Nat2Z.inj_pred_max Nat2Z.inj_min Nat2Z.inj_max Zabs2Nat.id_abs Zabs2Nat.id : pull_Zof_nat.
Hint Rewrite Z.shiftr_shiftl_l Z.shiftr_shiftl_r Z.shiftr_shiftr Z.shiftl_shiftl using zutil_arith : pull_Zshift.
Hint Rewrite <- Z.shiftr_lxor Z.shiftr_land Z.shiftr_lor Z.shiftr_ldiff Z.lnot_shiftr Z.ldiff_ones_r Z.shiftl_lxor Z.shiftl_land Z.shiftl_lor Z.shiftl_ldiff using zutil_arith : pull_Zshift.
Hint Rewrite Z.shiftr_lxor Z.shiftr_land Z.shiftr_lor Z.shiftr_ldiff Z.lnot_shiftr Z.ldiff_ones_r Z.shiftl_lxor Z.shiftl_land Z.shiftl_lor Z.shiftl_ldiff using zutil_arith : push_Zshift.
Hint Rewrite <- Z.shiftr_shiftl_l Z.shiftr_shiftl_r Z.shiftr_shiftr Z.shiftl_shiftl using zutil_arith : push_Zshift.
Hint Rewrite Z.shiftr_opp_r Z.shiftl_opp_r Z.shiftr_0_r Z.shiftr_0_l Z.shiftl_0_r Z.shiftl_0_l : push_Zshift.
Hint Rewrite Z.shiftl_1_l Z.shiftr_div_pow2 Z.shiftr_mul_pow2 Z.shiftl_mul_pow2 Z.shiftl_div_pow2 Z.opp_involutive using zutil_arith : Zshift_to_pow.
Hint Rewrite <- Z.shiftr_opp_r using zutil_arith : Zshift_to_pow.
Hint Rewrite <- Z.shiftr_div_pow2 Z.shiftr_mul_pow2 Z.shiftl_mul_pow2 Z.shiftl_div_pow2 using zutil_arith : Zpow_to_shift.
Hint Rewrite Z.add_max_distr_r Z.add_max_distr_l : push_Zmax.
Hint Rewrite <- Z.add_max_distr_r Z.add_max_distr_l : pull_Zmax.

(** For the occasional lemma that can remove the use of [Z.div] *)
Create HintDb zstrip_div.
Hint Rewrite Z.div_small_iff using zutil_arith : zstrip_div.

Hint Rewrite <- Z.shiftr_div_pow2 Z.shiftr_mul_pow2 Z.shiftl_mul_pow2 Z.shiftl_div_pow2 using zutil_arith : convert_to_Ztestbit.

(** It's not clear that [mod] is much easier for [lia] than [Z.div],
    so we separate out the transformations between [mod] and [div].
    We'll put, e.g., [mul_div_eq] into it below. *)
Create HintDb zstrip_div.

(** Work around bug #5019, that [zify] loops on dependent types.  We
    copy/paste [zify_nat_op] from the standard library and add a case
    to each of the [match isnat with ... end]. *)
Ltac zify_nat_op ::=
 match goal with
  (* misc type conversions: positive/N/Z to nat *)
  | H : context [ Z.of_nat (Pos.to_nat ?a) ] |- _ => rewrite (positive_nat_Z a) in H
  | |- context [ Z.of_nat (Pos.to_nat ?a) ] => rewrite (positive_nat_Z a)
  | H : context [ Z.of_nat (N.to_nat ?a) ] |- _ => rewrite (N_nat_Z a) in H
  | |- context [ Z.of_nat (N.to_nat ?a) ] => rewrite (N_nat_Z a)
  | H : context [ Z.of_nat (Z.abs_nat ?a) ] |- _ => rewrite (Zabs2Nat.id_abs a) in H
  | |- context [ Z.of_nat (Z.abs_nat ?a) ] => rewrite (Zabs2Nat.id_abs a)

  (* plus -> Z.add *)
  | H : context [ Z.of_nat (plus ?a ?b) ] |- _ => rewrite (Nat2Z.inj_add a b) in H
  | |- context [ Z.of_nat (plus ?a ?b) ] => rewrite (Nat2Z.inj_add a b)

  (* min -> Z.min *)
  | H : context [ Z.of_nat (min ?a ?b) ] |- _ => rewrite (Nat2Z.inj_min a b) in H
  | |- context [ Z.of_nat (min ?a ?b) ] => rewrite (Nat2Z.inj_min a b)

  (* max -> Z.max *)
  | H : context [ Z.of_nat (max ?a ?b) ] |- _ => rewrite (Nat2Z.inj_max a b) in H
  | |- context [ Z.of_nat (max ?a ?b) ] => rewrite (Nat2Z.inj_max a b)

  (* minus -> Z.max (Z.sub ... ...) 0 *)
  | H : context [ Z.of_nat (minus ?a ?b) ] |- _ => rewrite (Nat2Z.inj_sub_max a b) in H
  | |- context [ Z.of_nat (minus ?a ?b) ] => rewrite (Nat2Z.inj_sub_max a b)

  (* pred -> minus ... -1 -> Z.max (Z.sub ... -1) 0 *)
  | H : context [ Z.of_nat (pred ?a) ] |- _ => rewrite (pred_of_minus a) in H
  | |- context [ Z.of_nat (pred ?a) ] => rewrite (pred_of_minus a)

  (* mult -> Z.mul and a positivity hypothesis *)
  | H : context [ Z.of_nat (mult ?a ?b) ] |- _ =>
        pose proof (Nat2Z.is_nonneg (mult a b));
        rewrite (Nat2Z.inj_mul a b) in *
  | |- context [ Z.of_nat (mult ?a ?b) ] =>
        pose proof (Nat2Z.is_nonneg (mult a b));
        rewrite (Nat2Z.inj_mul a b) in *

  (* O -> Z0 *)
  | H : context [ Z.of_nat O ] |- _ => simpl (Z.of_nat O) in H
  | |- context [ Z.of_nat O ] => simpl (Z.of_nat O)

  (* S -> number or Z.succ *)
  | H : context [ Z.of_nat (S ?a) ] |- _ =>
     let isnat := isnatcst a in
     match isnat with
      | true => simpl (Z.of_nat (S a)) in H
      | _ => rewrite (Nat2Z.inj_succ a) in H
      | _ => change (Z.of_nat (S a)) with (Z_of_nat' (S a)) in H
     end
  | |- context [ Z.of_nat (S ?a) ] =>
     let isnat := isnatcst a in
     match isnat with
      | true => simpl (Z.of_nat (S a))
      | _ => rewrite (Nat2Z.inj_succ a)
      | _ => change (Z.of_nat (S a)) with (Z_of_nat' (S a))
     end

  (* atoms of type nat : we add a positivity condition (if not already there) *)
  | _ : 0 <= Z.of_nat ?a |- _ => hide_Z_of_nat a
  | _ : context [ Z.of_nat ?a ] |- _ =>
    pose proof (Nat2Z.is_nonneg a); hide_Z_of_nat a
  | |- context [ Z.of_nat ?a ] =>
    pose proof (Nat2Z.is_nonneg a); hide_Z_of_nat a
 end.

Create HintDb Ztestbit discriminated.
Create HintDb Ztestbit_full discriminated.
Hint Rewrite Z.testbit_0_l Z.land_spec Z.lor_spec : Ztestbit.
Hint Rewrite Z.testbit_0_l Z.land_spec Z.lor_spec : Ztestbit_full.
Hint Rewrite Z.shiftl_spec Z.shiftr_spec using zutil_arith : Ztestbit.
Hint Rewrite Z.testbit_neg_r using zutil_arith : Ztestbit.
Hint Rewrite Bool.andb_true_r Bool.andb_false_r Bool.orb_true_r Bool.orb_false_r
             Bool.andb_true_l Bool.andb_false_l Bool.orb_true_l Bool.orb_false_l : Ztestbit.
