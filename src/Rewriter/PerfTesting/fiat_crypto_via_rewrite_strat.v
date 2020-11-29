(** This file can be run interactively in emacs/PG from the
    fiat-crypto directory *)
(** If you want to use coqc, you must set [COQPATH] to the value
    emitted by [make printenv] in fiat-crypto, and then invoke [coqc
    -q -R /path/to/fiat-crypto/src Crypto /path/to/this-file.v]. *)
Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.QArith.QArith_base.
Require Import Crypto.Rewriter.PerfTesting.Core.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.ListUtil.
Import List.ListNotations.
Import UnsaturatedSolinas.
Local Open Scope list_scope.

Hint Rewrite <- pred_Sn : mydb.
Lemma Z_of_nat_O : Z.of_nat 0 = 0. Proof. reflexivity. Qed.
Hint Rewrite Z_of_nat_O : mydb.
Lemma Z_of_nat_S : forall x, Z.of_nat (S x) = Z.pos (Pos.of_succ_nat x). Proof. reflexivity. Qed.
Hint Rewrite Z_of_nat_S : mydb.
Hint Rewrite @Prod.fst_pair @Prod.snd_pair : mydb.
Lemma Z_mul_pos_pos x y : Z.pos x * Z.pos y = Z.pos (x * y). Proof. reflexivity. Qed.
Hint Rewrite Z_mul_pos_pos : mydb.
Hint Rewrite Z.mul_0_l Z.mul_0_r Z.opp_0 : mydb.
Lemma Z_div_0_l_pos x : 0 / Z.pos x = 0. Proof. reflexivity. Qed.
Hint Rewrite Z_div_0_l_pos : mydb.
Lemma Z_opp_pos x : Z.opp (Z.pos x) = Z.neg x. Proof. reflexivity. Qed.
Hint Rewrite Z_opp_pos : mydb.
Lemma Z_opp_neg x : Z.opp (Z.neg x) = Z.pos x. Proof. reflexivity. Qed.
Hint Rewrite Z_opp_neg : mydb.
Definition Z_div_unfolded := Eval cbv in Z.div.
Lemma unfold_Z_div_pos_pos x y : Z.div (Z.pos x) (Z.pos y) = Z_div_unfolded (Z.pos x) (Z.pos y).
Proof. reflexivity. Qed.
Lemma unfold_Z_div_pos_neg x y : Z.div (Z.pos x) (Z.neg y) = Z_div_unfolded (Z.pos x) (Z.neg y).
Proof. reflexivity. Qed.
Lemma unfold_Z_div_neg_pos x y : Z.div (Z.neg x) (Z.pos y) = Z_div_unfolded (Z.neg x) (Z.pos y).
Proof. reflexivity. Qed.
Lemma unfold_Z_div_neg_neg x y : Z.div (Z.neg x) (Z.neg y) = Z_div_unfolded (Z.neg x) (Z.neg y).
Proof. reflexivity. Qed.
Hint Rewrite unfold_Z_div_neg_neg unfold_Z_div_neg_pos unfold_Z_div_pos_neg unfold_Z_div_pos_pos : mydb.
Hint Rewrite Z.pow_0_r : mydb.
Definition Z_pow_unfolded := Eval cbv in Z.pow.
Lemma Z_pow_pos_pos x y : Z.pow (Z.pos x) (Z.pos y) = Z_pow_unfolded (Z.pos x) (Z.pos y). Proof. reflexivity. Qed.
Hint Rewrite Z_pow_pos_pos : mydb.
Lemma app_cons A (x : A) xs ys : (x :: xs) ++ ys = x :: (xs ++ ys).
Proof. reflexivity. Qed.
Hint Rewrite app_cons : mydb.
Lemma app_nil A xs : @nil A ++ xs = xs.
Proof. reflexivity. Qed.
Hint Rewrite app_nil : mydb.
Lemma partition_cons A f x xs : @partition A f (x :: xs) = prod_rect (fun _ => _) (fun g d => if f x then (x :: g, d) else (g, x :: d)) (partition f xs).
Proof. reflexivity. Qed.
Hint Rewrite partition_cons : mydb.
Lemma partition_nil A f : @partition A f nil = (nil, nil). Proof. reflexivity. Qed.
Hint Rewrite partition_nil : mydb.
Lemma prod_rect_pair A B P f x y : @prod_rect A B P f (x, y) = f x y. Proof. reflexivity. Qed.
Hint Rewrite prod_rect_pair : mydb.
Definition Z_modulo_unfolded := Eval cbv in Z.modulo.
Lemma Z_modulo_pos_pos x y : Z.modulo (Z.pos x) (Z.pos y) = Z_modulo_unfolded (Z.pos x) (Z.pos y).
Proof. reflexivity. Qed.
Hint Rewrite Z_modulo_pos_pos : mydb.
Hint Rewrite Z.eqb_refl Nat.eqb_refl : mydb.
Definition Pos_eqb_unfolded := Eval cbv in Pos.eqb.
Lemma Z_eqb_pos_pos x y : Z.eqb (Z.pos x) (Z.pos y) = Pos_eqb_unfolded x y. Proof. reflexivity. Qed.
Hint Rewrite Z_eqb_pos_pos : mydb.
Lemma Z_eqb_neg_neg x y : Z.eqb (Z.neg x) (Z.neg y) = Pos_eqb_unfolded x y. Proof. reflexivity. Qed.
Hint Rewrite Z_eqb_neg_neg : mydb.
Lemma Z_eqb_pos_0 x : Z.eqb (Z.pos x) 0 = false. Proof. reflexivity. Qed.
Hint Rewrite Z_eqb_pos_0 : mydb.
Lemma Z_eqb_0_pos x : Z.eqb 0 (Z.pos x) = false. Proof. reflexivity. Qed.
Hint Rewrite Z_eqb_0_pos : mydb.
Lemma Z_eqb_pos_neg x y : Z.eqb (Z.pos x) (Z.neg y) = false. Proof. reflexivity. Qed.
Hint Rewrite Z_eqb_pos_neg : mydb.
Lemma Z_eqb_neg_pos y x : Z.eqb (Z.neg y) (Z.pos x) = false. Proof. reflexivity. Qed.
Hint Rewrite Z_eqb_neg_pos : mydb.
Lemma Z_eqb_neg_0 x : Z.eqb (Z.neg x) 0 = false. Proof. reflexivity. Qed.
Hint Rewrite Z_eqb_neg_0 : mydb.
Lemma Z_eqb_0_neg x : Z.eqb 0 (Z.neg x) = false. Proof. reflexivity. Qed.
Hint Rewrite Z_eqb_0_neg : mydb.
Lemma length_nil A : List.length (@nil A) = 0%nat. Proof. reflexivity. Qed.
Hint Rewrite map_cons map_nil @length_cons length_nil : mydb.
Hint Rewrite @flat_map_cons @flat_map_nil : mydb.
Lemma nat_eqb_S_O x : Nat.eqb (S x) O = false. Proof. reflexivity. Qed.
Hint Rewrite nat_eqb_S_O : mydb.
Lemma nat_eqb_O_S x : Nat.eqb O (S x) = false. Proof. reflexivity. Qed.
Hint Rewrite nat_eqb_O_S : mydb.
Hint Rewrite @fold_right_cons @fold_right_nil : mydb.
Import Rewriter.Util.LetIn.
Lemma dlet_pair A B T x y f : Let_In (@pair A B x y) f = (dlet x' := x in dlet y' := y in f (x', y')) :> T.
Proof. reflexivity. Qed.
Hint Rewrite dlet_pair : mydb letdb.
Lemma lift_dlet A B C x (f : A -> B) (g : B -> C) : g (Let_In x f) = Let_In x (fun x' => g (f x')). Proof. reflexivity. Qed.
Hint Rewrite lift_dlet : mydb letdb.
Lemma lift_dlet1 A B C D x y (f : A -> B) (g : B -> C -> D) : g (Let_In x f) y = Let_In x (fun x' => g (f x') y). Proof. reflexivity. Qed.
Hint Rewrite lift_dlet1 : mydb letdb.
Lemma inline_dlet_S B x (f : nat -> B) : Let_In (S x) f = f (S x). Proof. reflexivity. Qed.
Hint Rewrite inline_dlet_S : mydb letdb.
Lemma inline_dlet_O B (f : nat -> B) : Let_In O f = f O. Proof. reflexivity. Qed.
Hint Rewrite inline_dlet_O : mydb letdb.
Lemma rev_nil A : rev (@nil A) = nil. Proof. reflexivity. Qed.
Hint Rewrite @rev_cons @rev_nil : mydb.
Hint Rewrite @update_nth_nil @update_nth_cons : mydb.
Lemma update_nth_S_cons T n f x xs : @update_nth T (S n) f (x :: xs) = x :: update_nth n f xs.
Proof. reflexivity. Qed.
Hint Rewrite update_nth_S_cons : mydb.
Hint Rewrite @combine_cons @combine_nil_r : mydb.
Lemma app_dlet A B x (f : A -> list B) ys : (Let_In x f) ++ ys = Let_In x (fun x' => f x' ++ ys).
Proof. reflexivity. Qed.
Hint Rewrite app_dlet : mydb letdb.
Lemma split_cons s p ps : Core.Associational.split s (p :: ps) = prod_rect (fun _ => _) (fun hi lo => (lo, List.map (fun t : Z * Z => (fst t / s, snd t)) hi)) (partition (fun t : Z * Z => fst t mod s =? 0) (p :: ps)).
Proof.
  cbv [Core.Associational.split prod_rect]; edestruct partition; reflexivity.
Qed.
Hint Rewrite split_cons : mydb.
Lemma mul_cons_cons p ps q qs : Core.Associational.mul (p :: ps) (q :: qs) = flat_map (fun t : Z * Z => List.map (fun t' : Z * Z => (fst t * fst t', snd t * snd t')) (q :: qs)) (p :: ps).
Proof. reflexivity. Qed.
Hint Rewrite mul_cons_cons : mydb.
Lemma mul_cons_nil p ps : Core.Associational.mul (p :: ps) nil = flat_map (fun t : Z * Z => List.map (fun t' : Z * Z => (fst t * fst t', snd t * snd t')) nil) (p :: ps).
Proof. reflexivity. Qed.
Hint Rewrite mul_cons_nil : mydb.
Lemma mul_nil_cons q qs : Core.Associational.mul nil (q :: qs) = flat_map (fun t : Z * Z => List.map (fun t' : Z * Z => (fst t * fst t', snd t * snd t')) (q :: qs)) nil.
Proof. reflexivity. Qed.
Hint Rewrite mul_nil_cons : mydb.
Lemma mul_nil_nil : Core.Associational.mul nil nil = flat_map (fun t : Z * Z => List.map (fun t' : Z * Z => (fst t * fst t', snd t * snd t')) nil) nil.
Proof. reflexivity. Qed.
Hint Rewrite mul_nil_nil : mydb.
Lemma unfold_reduce s c p : Core.Associational.reduce s c p = prod_rect (fun _ => _) (fun lo hi => lo ++ Core.Associational.mul c hi) (Core.Associational.split s p).
Proof. cbv [Core.Associational.reduce]; edestruct Core.Associational.split; reflexivity. Qed.
Hint Rewrite unfold_reduce : mydb.
Lemma nat_rect_O P fO fS : nat_rect P fO fS 0 = fO.
Proof. reflexivity. Qed.
Hint Rewrite nat_rect_O : mydb.
Lemma nat_rect_O_arr P Q fO fS x : nat_rect (fun n => P n -> Q n) fO fS 0 x = fO x.
Proof. reflexivity. Qed.
Hint Rewrite nat_rect_O_arr : mydb.
Lemma nat_rect_S P fO fS n : nat_rect P fO fS (S n) = fS n (nat_rect P fO fS n).
Proof. reflexivity. Qed.
Hint Rewrite nat_rect_S : mydb.
Lemma nat_rect_S_arr P Q fO fS n x : nat_rect (fun n => P n -> Q n) fO fS (S n) x = fS n (nat_rect _ fO fS n) x.
Proof. reflexivity. Qed.
Hint Rewrite nat_rect_S_arr : mydb.

Declare Reduction mycbv := cbv [Pos.of_succ_nat Pos.succ Pos.mul Pos.add Z_div_unfolded Z_pow_unfolded Z_modulo_unfolded Pos_eqb_unfolded].
Ltac mycbv := cbv [Pos.of_succ_nat Pos.succ Pos.mul Pos.add Z_div_unfolded Z_pow_unfolded Z_modulo_unfolded Pos_eqb_unfolded].

Declare Reduction morecbv := cbv [Core.Associational.repeat_reduce Core.Positional.from_associational Core.Positional.zeros repeat Core.Positional.place Core.Positional.chained_carries Core.Positional.add_to_nth Core.Positional.carry_reduce Core.Positional.carry Core.Positional.to_associational seq Core.Associational.carry Core.Associational.carryterm].
Ltac morecbv := cbv [Core.Associational.repeat_reduce Core.Positional.from_associational Core.Positional.zeros repeat Core.Positional.place Core.Positional.chained_carries Core.Positional.add_to_nth Core.Positional.carry_reduce Core.Positional.carry Core.Positional.to_associational seq Core.Associational.carry Core.Associational.carryterm].

Opaque LetIn.Let_In.
Hint Constants Opaque : rewrite.

Global Instance: forall A B, Proper (eq ==> eq ==> eq) (@pair A B) := _.
Global Instance: forall A B P, Proper (pointwise_relation _ (pointwise_relation _ eq) ==> eq ==> eq) (@prod_rect A B (fun _ => P)).
Proof. intros ? ? ? f g Hfg [? ?] ? ?; subst; apply Hfg. Qed.
Global Instance: Transitive (Basics.flip Basics.impl) := _.
Existing Instance pointwise_map.
Existing Instance fold_right_Proper.
Global Instance: forall A B, Proper (forall_relation (fun _ => pointwise_relation _ eq) ==> eq ==> eq ==> eq) (@fold_right A B).
Proof. intros ? ? f g Hfg. apply fold_right_Proper, Hfg. Qed.
Global Instance: forall A B x, (Proper (pointwise_relation _ eq ==> eq) (@Let_In A (fun _ => B) x)) := _.
Global Instance:
  forall A B,
    Proper
      ((eq ==> eq)
         ==> (eq ==> (eq ==> eq) ==> eq ==> eq)
         ==> eq
         ==> eq
         ==> eq)
      (nat_rect (fun _ => A -> B)).
Proof.
  cbv -[nat_rect]; intros ???????? n n' ? y y' ?; subst n' y'; subst; revert y.
  induction n; cbn; intros; eauto.
  match goal with H : _ |- _ => apply H; intuition (subst; eauto) end.
Qed.

Definition p' := Eval vm_compute in of_string "2^190 - 11" 64.
Definition p : params
  := Eval vm_compute in invert_Some (List.nth_error p' 0).
Existing Instance p.

Goal True.
  pose (fun f g : list Z => Arithmetic.ModOps.carry_mulmod (Qnum limbwidth) (Zpos (Qden limbwidth)) s c n idxs (ListUtil.expand_list 0 f n) (ListUtil.expand_list 0 g n)) as v.
  cbv -[ModOps.carry_mulmod ListUtil.expand_list] in v.
  assert (forall f g, v f g = f); subst v; intros.
  { cbv [ListUtil.expand_list ModOps.carry_mulmod ListUtil.expand_list_helper nat_rect Arithmetic.ModOps.weight Core.Positional.mulmod Core.Positional.to_associational seq List.map List.combine Core.Associational.mul flat_map].
    Set Ltac Profiling.
    Ltac go_step :=
      time (match goal with |- ?G => idtac "Goal:" G end;
                   first [ time setoid_rewrite lift_dlet
                         | time setoid_rewrite lift_dlet1
                         | match goal with
                           | [ |- context[Let_In _ _ ++ _] ] => setoid_rewrite app_dlet
                           | [ |- context[dlet x := (_, _) in _] ] => setoid_rewrite dlet_pair
                           | [ |- context[Let_In O] ] => setoid_rewrite inline_dlet_O
                           | [ |- context[Let_In (S ?x)] ] => setoid_rewrite inline_dlet_S
                           end
                         | time progress mycbv
                         | time progress rewrite ?Z_of_nat_O, ?Z_of_nat_S, ?Z_mul_pos_pos, ?Z.mul_0_l, ?Z.mul_0_r, ?Z.opp_0, ?Z_div_0_l_pos, ?Z_opp_pos, ?Z_opp_neg, ?unfold_Z_div_pos_pos, ?unfold_Z_div_pos_neg, ?unfold_Z_div_neg_pos,?unfold_Z_div_neg_neg, ?Z.pow_0_r, ?Z_pow_pos_pos, ?Z_modulo_pos_pos, ?Z_eqb_pos_pos, ?Z.eqb_refl, ?Nat.eqb_refl, ?Z_eqb_neg_neg, ?Z_eqb_pos_0, ?Z_eqb_0_pos, ?Z_eqb_pos_neg, ?Z_eqb_neg_pos, ?Z_eqb_neg_0, ?Z_eqb_0_neg, ?length_nil, <- ?pred_Sn, ?nat_eqb_S_O, ?nat_eqb_O_S
                         | progress cbn [nat_rect]
                         | match goal with
                           | [ |- context[prod_rect _ (_, _)] ] => setoid_rewrite prod_rect_pair
                           | [ |- context[List.length (_ :: _)] ] => setoid_rewrite @length_cons
                           | [ |- context[fst (_, _)] ] => setoid_rewrite @Prod.fst_pair
                           | [ |- context[snd (_, _)] ] => setoid_rewrite @Prod.snd_pair
                           | [ |- context[(_ :: _) ++ _] ] => setoid_rewrite app_cons
                           | [ |- context[nil ++ _] ] => setoid_rewrite app_nil
                           | [ |- context[rev (_ :: _)] ] => setoid_rewrite rev_cons
                           | [ |- context[rev nil] ] => setoid_rewrite rev_nil
                           | [ |- context[prod_rect _ _ (_, _)] ] => setoid_rewrite prod_rect_pair
                           | [ |- context[partition _ nil] ] => setoid_rewrite partition_nil
                           | [ |- context[fold_right _ _ nil] ] => setoid_rewrite @fold_right_nil
                           | [ |- context[update_nth _ _ nil] ] => setoid_rewrite @update_nth_nil
                           | [ |- context[update_nth O _ (_ :: _)] ] => setoid_rewrite @update_nth_cons
                           | [ |- context[update_nth (S _) _ (_ :: _)] ] => setoid_rewrite @update_nth_S_cons
                           | [ |- context[List.map _ nil] ] => setoid_rewrite map_nil
                           | [ |- context[List.combine _ nil] ] => setoid_rewrite @combine_nil_r
                           | [ |- context[flat_map _ nil] ] => setoid_rewrite @flat_map_nil
                           | [ |- context[partition _ (_ :: _)] ] => setoid_rewrite partition_cons
                           | [ |- context[fold_right _ _ (_ :: _)] ] => setoid_rewrite @fold_right_cons
                           | [ |- context[List.map _ (_ :: _)] ] => setoid_rewrite map_cons
                           | [ |- context[List.combine (_ :: _) (_ :: _)] ] => setoid_rewrite @combine_cons
                           | [ |- context[flat_map _ (_ :: _)] ] => setoid_rewrite @flat_map_cons
                           | [ |- context[Core.Associational.split _ (_ :: _)] ] => setoid_rewrite split_cons
                           | [ |- context[Core.Associational.reduce _ _ _] ] => setoid_rewrite unfold_reduce
                           | [ |- context[Core.Associational.mul (_ :: _) (_ :: _)] ] => setoid_rewrite mul_cons_cons
                           | [ |- context[Core.Associational.mul nil (_ :: _)] ] => setoid_rewrite mul_nil_cons
                           | [ |- context[Core.Associational.mul (_ :: _) nil] ] => setoid_rewrite mul_cons_nil
                           | [ |- context[Core.Associational.mul nil nil] ] => setoid_rewrite mul_nil_nil
                           | [ |- context[nat_rect _ _ _ O _] ] => idtac "0arr"; setoid_rewrite nat_rect_O_arr
                           | [ |- context[nat_rect _ _ _ (S _) _] ] => idtac "Sarr"; setoid_rewrite nat_rect_S_arr
                           | [ |- context[nat_rect _ _ _ (S _)] ] => idtac "S"; setoid_rewrite nat_rect_S
                           | [ |- context[nat_rect _ _ _ O] ] => idtac "0"; setoid_rewrite nat_rect_O
                           end
                         | progress cbv [Core.Associational.repeat_reduce]
                         | progress cbv [Core.Positional.from_associational]
                         | progress cbv [Core.Positional.zeros repeat]
                         | progress cbv [Core.Positional.place]
                         | progress cbv [Core.Positional.chained_carries]
                         | progress cbv [Core.Positional.add_to_nth]
                         | progress cbv [Core.Positional.carry_reduce Core.Positional.carry Core.Positional.to_associational seq Core.Associational.carry Core.Associational.carryterm] ]).
    Ltac go_count n := idtac "Cur:" n; tryif go_step then go_count (S n) else idtac "Finished:" n.
    Ltac go := go_count O (*repeat go_step*).
    Set Printing Depth 1000000.
    Time go.
    (* size 1: Finished transaction in 100.141 secs (99.967u,0.171s) (successful) *)
    (* Size 2: Finished transaction in 607.765 secs (606.448u,1.267s) (successful), Finished: 1269%nat *)
    (* size 3: Finished transaction in 8706.089 secs (8692.561u,13.515s) (successful), Finished: 2398%nat, src/Rewriter/PerfTesting/fiat_crypto_via_rewrite_strat.vo (real: 8711.19, user: 8695.54, sys: 15.63, mem: 58206840 ko) *)

    (* Size 3 end:
Goal: ((dlet y' : Z := 1 * (nth_default 0 f 0 * nth_default 0 g 0) in
        dlet x' : Z := 1 * (nth_default 0 f 0 * nth_default 0 g 1) in
        dlet x'0 : Z := 1 * (nth_default 0 f 0 * nth_default 0 g 2) in
        dlet x'1 : Z := 1 * (nth_default 0 f 1 * nth_default 0 g 0) in
        dlet x'2 : Z := 2 * (nth_default 0 f 1 * nth_default 0 g 1) in
        dlet x'3 : Z := 1 * (nth_default 0 f 2 * nth_default 0 g 0) in
        dlet x'4 : Z := 2 * (5 * (nth_default 0 f 1 * nth_default 0 g 2)) in
        dlet x'5 : Z := 2 * (5 * (nth_default 0 f 2 * nth_default 0 g 1)) in
        dlet x'6 : Z := 1 * (5 * (nth_default 0 f 2 * nth_default 0 g 2)) in
        dlet x'7 : Z := y' + (x'4 + (x'5 + 0)) in
        dlet x'8 : Z := x'7 / 17592186044416 in
        dlet x'9 : Z := x'7 mod 17592186044416 in
        dlet y'0 : Z := 1 * x'8 in
        dlet y'1 : Z := 1 * x'9 in
        dlet y'2 : Z := 1 * (x' + (x'1 + (x'6 + 0))) in
        dlet y'3 : Z := 1 * (x'0 + (x'2 + (x'3 + 0))) in
        dlet y'4 : Z := 1 * (y'1 + 0) in
        dlet y'5 : Z := 1 * (y'0 + (y'2 + 0)) in
        dlet y'6 : Z := 1 * (y'3 + 0) in
        dlet y'7 : Z := 0 in
        dlet y'8 : Z := 1 * (y'4 + (y'7 + 0)) in
        dlet x'10 : Z := y'5 + 0 in
        dlet x'11 : Z := x'10 / 8796093022208 in
        dlet x'12 : Z := x'10 mod 8796093022208 in
        dlet y'9 : Z := 1 * x'11 in
        dlet y'10 : Z := 1 * x'12 in
        dlet y'11 : Z := 1 * (y'6 + 0) in
        dlet y'12 : Z := 1 * (y'8 + 0) in
        dlet y'13 : Z := 1 * (y'10 + 0) in
        dlet y'14 : Z := 1 * (y'9 + (y'11 + 0)) in
        dlet y'15 : Z := 0 in
        dlet y'16 : Z := 1 * (y'12 + (y'15 + 0)) in
        dlet y'17 : Z := 1 * (y'13 + 0) in
        dlet x'13 : Z := y'14 + 0 in
        dlet x'14 : Z := x'13 / 8796093022208 in
        dlet x'15 : Z := x'13 mod 8796093022208 in
        dlet y'18 : Z := 1 * x'14 in
        dlet y'19 : Z := 1 * x'15 in
        dlet y'20 : Z := 1 * (y'16 + 0) in
        dlet y'21 : Z := 1 * (y'17 + 0) in
        dlet y'22 : Z := 1 * (y'19 + 0) in
        dlet y'23 : Z := 1 * (5 * (y'18 + 0)) in
        dlet x'16 : Z := y'20 + (y'23 + 0) in
        dlet x'17 : Z := x'16 / 17592186044416 in
        dlet x'18 : Z := x'16 mod 17592186044416 in
        dlet y'24 : Z := 1 * x'17 in
        dlet y'25 : Z := 1 * x'18 in
        dlet y'26 : Z := 1 * (y'21 + 0) in
        dlet y'27 : Z := 1 * (y'22 + 0) in
        dlet y'28 : Z := 1 * (y'25 + 0) in
        dlet y'29 : Z := 1 * (y'24 + (y'26 + 0)) in
        dlet y'30 : Z := 1 * (y'27 + 0) in
        dlet y'31 : Z := 0 in
        dlet y'32 : Z := 1 * (y'28 + (y'31 + 0)) in
        dlet x'19 : Z := y'29 + 0 in
        dlet x'20 : Z := x'19 / 8796093022208 in
        dlet x'21 : Z := x'19 mod 8796093022208 in
        dlet y'33 : Z := 1 * x'20 in
        dlet y'34 : Z := 1 * x'21 in
        dlet y'35 : Z := 1 * (y'30 + 0) in
        dlet y'36 : Z := 1 * (y'32 + 0) in
        dlet y'37 : Z := 1 * (y'34 + 0) in
        dlet y'38 : Z := 1 * (y'33 + (y'35 + 0)) in
        dlet y'39 : Z := 0 in
        [y'36 + (y'39 + 0); y'37 + 0; y'38 + 0]) = f)
*)
    Show.
Abort.
(*
    Time (rewrite_strat (((topdown (hints mydb; eval mycbv));
                            eval cbv [Core.Associational.repeat_reduce nat_rect Core.Associational.split Core.Associational.mul];
                            ((topdown (hints mydb; eval mycbv)));
                            eval cbv [Core.Positional.from_associational Init.Nat.pred Core.Positional.zeros repeat Core.Positional.place nat_rect Core.Positional.add_to_nth])));
      (* COQBUG(https://github.com/coq/coq/issues/10934) *)
      (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv)))));
      (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv)))));
      (rewrite_strat eval cbv [Core.Positional.chained_carries Core.Positional.carry_reduce]);
      (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv)))));
      (rewrite_strat eval cbv [Core.Positional.carry Core.Positional.to_associational Core.Associational.carry seq Core.Associational.carryterm Core.Positional.from_associational]);
      (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv)))));(*.
        Time*)
      (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv)))));(*.
        Time*)
      (rewrite_strat eval cbv [Init.Nat.pred Core.Positional.zeros repeat Core.Positional.place nat_rect]);
      (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv)))));(*.
        Time*)
      (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv)))));
      (rewrite_strat eval cbv [Core.Positional.add_to_nth Core.Associational.reduce]);(*.
        Set Printing Depth 1000000.
        Typeclasses eauto := debug.
        Time*)
      (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv)))));(*.
        Time*)
      (rewrite_strat ((try repeat (topdown (hints mydb; eval mycbv))))).
    Show.
Abort.
*)
