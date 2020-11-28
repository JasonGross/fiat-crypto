Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.AddGetCarry Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.
Require Import Crypto.Arithmetic.SaturatedAssociational.

Module Columns.
  Import Weight.
  Section Columns.
    Context weight {wprops : @weight_properties weight}.

    Definition eval n (x : list (list Z)) : Z := Positional.eval weight n (map sum x).

    Lemma eval_nil n : eval n [] = 0.
    Proof using Type. cbv [eval]; simpl. apply Positional.eval_nil. Qed.
    Hint Rewrite eval_nil : push_eval.
    Lemma eval_snoc n x y : n = length x -> eval (S n) (x ++ [y]) = eval n x + weight n * sum y.
    Proof using Type.
      cbv [eval]; intros; subst. rewrite map_app. simpl map.
      apply Positional.eval_snoc; distr_length.
    Qed. Hint Rewrite eval_snoc using (solve [distr_length]) : push_eval.

    Ltac cases :=
      match goal with
      | |- _ /\ _ => split
      | H: _ /\ _ |- _ => destruct H
      | H: _ \/ _ |- _ => destruct H
      | _ => progress break_match; try discriminate
      end.

    Section Flatten.
      Context (add_split : Z -> Z -> Z -> Z * Z).
      Context (add_split_mod :
                 forall s x y, fst (add_split s x y) = (x + y) mod s)
              (add_split_div :
                 forall s x y, snd (add_split s x y) = (x + y) / s).
      Hint Rewrite add_split_mod add_split_div : to_div_mod.

      Section flatten_column.
        Context (fw : Z). (* maximum size of the result *)

        (* Outputs (sum, carry) *)
        Definition flatten_column (digit: list Z) : (Z * Z) :=
          list_rect (fun _ => (Z * Z)%type) (0,0)
                    (fun x tl flatten_column_tl =>
                       list_case
                         (fun _ => (Z * Z)%type) (x mod fw, x / fw)
                         (fun y tl' =>
                            list_case
                              (fun _ => (Z * Z)%type) (add_split fw x y)
                              (fun _ _ =>
                                 dlet_nd rec := flatten_column_tl in (* recursively get the sum and carry *)
                                   dlet_nd sum_carry := add_split fw x (fst rec) in (* add the new value to the sum *)
                                   dlet_nd carry' := snd sum_carry + snd rec in (* add the two carries together *)
                                   (fst sum_carry, carry'))
                              tl')
                         tl)
                    digit.
      End flatten_column.

      Definition flatten_step (digit:list Z) (acc_carry:list Z * Z) : list Z * Z :=
        let acc := fst acc_carry in
        let carry := snd acc_carry in
        let fw := weight (S (length acc)) / weight (length acc) in
        dlet sum_carry := flatten_column fw (digit ++ [snd acc_carry]) in
              (acc ++ fst sum_carry :: nil, snd sum_carry).

      Definition flatten (xs : list (list Z)) : list Z * Z :=
        fold_right (fun a b => flatten_step a b) (nil,0) (rev xs).

      Ltac push_fast :=
        repeat match goal with
               | _ => progress cbv [Let_In list_case]
               | |- context [list_rect _ _ _ ?ls] => rewrite single_list_rect_to_match; destruct ls
               | _ => progress (unfold flatten_step in *; fold flatten_step in * )
               | _ => rewrite Nat.add_1_r
               | _ => rewrite Z.mul_div_eq_full by (auto with zarith; lia)
               | _ => rewrite weight_multiples
               | _ => reflexivity
               | _ => solve [repeat (f_equal; try ring)]
               | _ => congruence
               | _ => progress cases
               end.
      Ltac push :=
        repeat match goal with
               | _ => progress push_fast
               | _ => progress autorewrite with cancel_pair to_div_mod
               | _ => progress autorewrite with push_sum push_fold_right push_nth_default in *
               | _ => progress autorewrite with pull_Zmod pull_Zdiv zsimplify_fast
               | _ => progress autorewrite with list distr_length push_eval
               end.

      Lemma flatten_column_mod fw (xs : list Z) :
        fst (flatten_column fw xs)  = sum xs mod fw.
      Proof using add_split_mod.
        induction xs; simpl flatten_column; cbv [Let_In];
          repeat match goal with
                 | _ => rewrite IHxs
                 | _ => progress push
                 end.
      Qed. Hint Rewrite flatten_column_mod : to_div_mod.

      Lemma flatten_column_div fw (xs : list Z) (fw_nz : fw <> 0) :
        snd (flatten_column fw xs)  = sum xs / fw.
      Proof using add_split_div add_split_mod.
        (* this hint is already in the database but Z.div_add_l' is triggered first and that screws things up *)
        Hint Rewrite <- Z.div_add' using zutil_arith : pull_Zdiv.
        induction xs; simpl flatten_column; cbv [Let_In];
          repeat match goal with
                 | _ => rewrite IHxs
                 | _ => rewrite <-Z.div_add' by zutil_arith
                 | _ => rewrite Z.mul_div_eq_full by lia
                 | _ => progress push
                 end.
      Qed. Hint Rewrite flatten_column_div using auto with zarith : to_div_mod.

      Hint Rewrite Positional.eval_nil : push_eval.

      Lemma length_flatten_step digit state :
        length (fst (flatten_step digit state)) = S (length (fst state)).
      Proof using add_split_mod. cbv [flatten_step]; push. Qed.
      Hint Rewrite length_flatten_step : distr_length.
      Lemma length_flatten inp : length (fst (flatten inp)) = length inp.
      Proof using add_split_mod.
        cbv [flatten]. induction inp using rev_ind; push.
      Qed.
      Hint Rewrite length_flatten : distr_length.

      Lemma flatten_snoc x inp : flatten (inp ++ [x]) = flatten_step x (flatten inp).
      Proof using Type. cbv [flatten]. rewrite rev_unit. reflexivity. Qed.

      Lemma flatten_correct inp:
        forall n,
          length inp = n ->
          flatten inp = (Partition.partition weight n (eval n inp),
                         eval n inp / (weight n)).
      Proof using wprops add_split_mod add_split_div.
        induction inp using rev_ind; intros;
          destruct n; distr_length; [ reflexivity | ].
        rewrite flatten_snoc.
        rewrite partition_step.
        erewrite IHinp with (n:=n) by distr_length.
        push.
        pose proof (@weight_positive _ wprops n).
        repeat match goal with
               | |- pair _ _ = pair _ _ => f_equal
               | |- _ ++ _ = _ ++ _ => f_equal
               | |- _ :: _ = _ :: _ => f_equal
               | _ => apply (@partition_eq_mod _ wprops)
               | _ => rewrite length_partition
               | _ => rewrite weight_mod_pull_div by auto
               | _ => rewrite weight_div_pull_div by auto
               | _ => f_equal; ring
               | _ => progress autorewrite with zsimplify
               end.
      Qed.

      Lemma flatten_div_mod n inp :
        length inp = n ->
        (Positional.eval weight n (fst (flatten inp))
         = (eval n inp) mod (weight n))
        /\ (snd (flatten inp) = eval n inp / weight n).
      Proof using wprops add_split_mod add_split_div.
        intros.
        rewrite flatten_correct with (n:=n) by auto.
        cbn [fst snd].
        rewrite eval_partition; auto.
      Qed.

      Lemma flatten_mod {n} inp :
        length inp = n ->
        (Positional.eval weight n (fst (flatten inp)) = (eval n inp) mod (weight n)).
      Proof using wprops add_split_mod add_split_div.
        apply flatten_div_mod.
      Qed.
      Hint Rewrite @flatten_mod : push_eval.

      Lemma flatten_div {n} inp :
        length inp = n -> snd (flatten inp) = eval n inp / weight n.
      Proof using wprops add_split_mod add_split_div.
        apply flatten_div_mod.
      Qed.
      Hint Rewrite @flatten_div : push_eval.

      Lemma flatten_same_sum p q :
        Forall2 (fun x y => sum x = sum y) p q ->
        flatten p = flatten q.
      Proof using wprops add_split_mod add_split_div.
        cbv [flatten].
        let H := fresh in
        intro H; apply Forall2_rev in H;
          induction H; [ reflexivity | ].
        push.
      Qed.
    End Flatten.

    Section FromAssociational.
      (* nils *)
      Definition nils n : list (list Z) := repeat nil n.
      Lemma length_nils n : length (nils n) = n. Proof using Type. cbv [nils]. distr_length. Qed.
      Hint Rewrite length_nils : distr_length.
      Lemma eval_nils n : eval n (nils n) = 0.
      Proof using Type.
        erewrite <-Positional.eval_zeros by eauto.
        cbv [eval nils]; rewrite List.map_repeat; reflexivity.
      Qed. Hint Rewrite eval_nils : push_eval.

      (* cons_to_nth *)
      Definition cons_to_nth i x (xs : list (list Z)) : list (list Z) :=
        ListUtil.update_nth i (fun y => cons x y) xs.
      Lemma length_cons_to_nth i x xs : length (cons_to_nth i x xs) = length xs.
      Proof using Type. cbv [cons_to_nth]. distr_length. Qed.
      Hint Rewrite length_cons_to_nth : distr_length.
      Lemma cons_to_nth_add_to_nth xs : forall i x,
          map sum (cons_to_nth i x xs) = Positional.add_to_nth i x (map sum xs).
      Proof using Type.
        cbv [cons_to_nth]; induction xs as [|? ? IHxs];
          intros i x; destruct i; simpl; rewrite ?IHxs; reflexivity.
      Qed.
      Lemma eval_cons_to_nth n i x xs : (i < length xs)%nat -> length xs = n ->
                                        eval n (cons_to_nth i x xs) = weight i * x + eval n xs.
      Proof using Type.
        cbv [eval]; intros. rewrite cons_to_nth_add_to_nth.
        apply Positional.eval_add_to_nth; distr_length.
      Qed. Hint Rewrite eval_cons_to_nth using (solve [distr_length]) : push_eval.

      Hint Rewrite Positional.eval_zeros : push_eval.
      Hint Rewrite Positional.eval_add_to_nth using (solve [distr_length]): push_eval.

      (* from_associational *)
      Definition from_associational n (p:list (Z*Z)) : list (list Z) :=
        List.fold_right (fun t ls =>
                           dlet_nd p := Positional.place weight t (pred n) in
                           cons_to_nth (fst p) (snd p) ls ) (nils n) p.
      Lemma length_from_associational n p : length (from_associational n p) = n.
      Proof using Type. cbv [from_associational Let_In]. apply fold_right_invariant; intros; distr_length. Qed.
      Hint Rewrite length_from_associational: distr_length.
      Lemma eval_from_associational n p (n_nonzero:n<>0%nat\/p=nil) :
        eval n (from_associational n p) = Associational.eval p.
      Proof using wprops.
        erewrite <-Positional.eval_from_associational by eauto with zarith.
        induction p; [ autorewrite with push_eval; solve [auto] |].
        cbv [from_associational Positional.from_associational]; autorewrite with push_fold_right.
        fold (from_associational n p); fold (Positional.from_associational weight n p).
        cbv [Let_In].
        match goal with |- context [Positional.place _ ?x ?n] =>
                        pose proof (Positional.place_in_range weight x n) end.
        repeat match goal with
               | _ => rewrite Nat.succ_pred in * by auto
               | _ => rewrite IHp by auto
               | _ => progress autorewrite with push_eval
               | _ => progress cases
               | _ => congruence
               end.
      Qed.

      Lemma from_associational_step n t p :
        from_associational n (t :: p) =
        cons_to_nth (fst (Positional.place weight t (Nat.pred n)))
                    (snd (Positional.place weight t (Nat.pred n)))
                    (from_associational n p).
      Proof using Type. reflexivity. Qed.
    End FromAssociational.

    Section Reverse.
      Definition reverse (p : list (list Z)) : list (list Z) :=
        map (@rev Z) p.

      Lemma eval_reverse n p :
        eval n (reverse p) = eval n p.
      Proof.
        cbv [eval reverse]. rewrite map_map.
        f_equal. apply map_ext; intros.
        autorewrite with push_sum. reflexivity.
      Qed. Hint Rewrite @eval_reverse : push_eval.

      Lemma length_reverse p :
        length (reverse p) = length p.
      Proof. cbv [reverse]; distr_length. Qed.
      Hint Rewrite @length_reverse : distr_length.

      Lemma reverse_same_sum p :
        Forall2 (fun x y => sum x = sum y) (reverse p) p.
      Proof.
        cbv [reverse].
        induction p; cbn [rev map]; constructor;
          autorewrite with push_sum; auto.
      Qed.
    End Reverse.
  End Columns.
End Columns.
