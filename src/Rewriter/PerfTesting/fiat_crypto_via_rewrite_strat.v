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

Definition p : params
  := Eval vm_compute in invert_Some (List.nth_error (of_string "2^5-3" 8) 0).
Existing Instance p.

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
Hint Rewrite dlet_pair : mydb.
Lemma lift_dlet A B C x (f : A -> B) (g : B -> C) : g (Let_In x f) = Let_In x (fun x' => g (f x)). Proof. reflexivity. Qed.
Hint Rewrite lift_dlet : mydb.
Lemma inline_dlet_S B x (f : nat -> B) : Let_In (S x) f = f (S x). Proof. reflexivity. Qed.
Hint Rewrite inline_dlet_S : mydb.
Lemma inline_dlet_O B (f : nat -> B) : Let_In O f = f O. Proof. reflexivity. Qed.
Hint Rewrite inline_dlet_O : mydb.
Lemma rev_nil A : rev (@nil A) = nil. Proof. reflexivity. Qed.
Hint Rewrite @rev_cons @rev_nil : mydb.
Hint Rewrite @update_nth_nil @update_nth_cons : mydb.
Lemma update_nth_S_cons T n f x xs : @update_nth T (S n) f (x :: xs) = x :: update_nth n f xs.
Proof. reflexivity. Qed.
Hint Rewrite update_nth_S_cons : mydb.
Hint Rewrite @combine_cons @combine_nil_r : mydb.
Lemma app_dlet A B x (f : A -> list B) ys : (Let_In x f) ++ ys = Let_In x (fun x' => f x' ++ ys).
Proof. reflexivity. Qed.
Hint Rewrite app_dlet : mydb.
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

Declare Reduction mycbv := cbv [Pos.of_succ_nat Pos.succ Pos.mul Pos.add Z_div_unfolded Z_pow_unfolded Z_modulo_unfolded Pos_eqb_unfolded].

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

Goal True.
  pose (fun f g : list Z => Arithmetic.ModOps.carry_mulmod (Qnum limbwidth) (Zpos (Qden limbwidth)) s c n idxs (ListUtil.expand_list 0 f n) (ListUtil.expand_list 0 g n)) as v.
  cbv -[ModOps.carry_mulmod ListUtil.expand_list] in v.
  assert (forall f g, v f g = f); subst v; intros.
  { cbv [ListUtil.expand_list ModOps.carry_mulmod ListUtil.expand_list_helper nat_rect Arithmetic.ModOps.weight Core.Positional.mulmod Core.Positional.to_associational seq List.map List.combine Core.Associational.mul flat_map].
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
