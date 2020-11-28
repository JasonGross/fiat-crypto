(* Following http://adam.chlipala.net/theses/andreser.pdf chapter 3 *)
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Structures.Orders.
Require Import Coq.Lists.List.
Require Import Crypto.Algebra.Nsatz.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Decidable.Bool2Prop.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Modulo.PullPush.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

Module Associational.
  Definition eval (p:list (Z*Z)) : Z :=
    fold_right (fun x y => x + y) 0%Z (map (fun t => fst t * snd t) p).

  Lemma eval_nil : eval nil = 0.
  Proof. trivial.                                             Qed.
  Lemma eval_cons p q : eval (p::q) = fst p * snd p + eval q.
  Proof. trivial.                                             Qed.
  Lemma eval_app p q: eval (p++q) = eval p + eval q.
  Proof. induction p; rewrite <-?List.app_comm_cons;
           rewrite ?eval_nil, ?eval_cons; nsatz.              Qed.

  Hint Rewrite eval_nil eval_cons eval_app : push_eval.
  Local Ltac push := autorewrite with
      push_eval push_map push_partition push_flat_map
      push_fold_right push_nth_default cancel_pair.

  Lemma eval_map_mul (a x:Z) (p:list (Z*Z))
  : eval (List.map (fun t => (a*fst t, x*snd t)) p) = a*x*eval p.
  Proof. induction p; push; nsatz.                            Qed.
  Hint Rewrite eval_map_mul : push_eval.

  Definition mul (p q:list (Z*Z)) : list (Z*Z) :=
    flat_map (fun t =>
      map (fun t' =>
        (fst t * fst t', snd t * snd t'))
    q) p.
  Lemma eval_mul p q : eval (mul p q) = eval p * eval q.
  Proof. induction p; cbv [mul]; push; nsatz.                 Qed.
  Hint Rewrite eval_mul : push_eval.

  Definition square (p:list (Z*Z)) : list (Z*Z) :=
    list_rect
      _
      nil
      (fun t ts acc
       => (dlet two_t2 := 2 * snd t in
               (fst t * fst t, snd t * snd t)
                 :: (map (fun t'
                          => (fst t * fst t', two_t2 * snd t'))
                         ts))
            ++ acc)
      p.
  Lemma eval_square p : eval (square p) = eval p * eval p.
  Proof. induction p; cbv [square list_rect Let_In]; push; nsatz. Qed.
  Hint Rewrite eval_square : push_eval.

  Definition negate_snd (p:list (Z*Z)) : list (Z*Z) :=
    map (fun cx => (fst cx, -snd cx)) p.
  Lemma eval_negate_snd p : eval (negate_snd p) = - eval p.
  Proof. induction p; cbv [negate_snd]; push; nsatz.          Qed.
  Hint Rewrite eval_negate_snd : push_eval.

  Example base10_2digit_mul (a0:Z) (a1:Z) (b0:Z) (b1:Z) :
    {ab| eval ab = eval [(10,a1);(1,a0)] * eval [(10,b1);(1,b0)]}.
    eexists ?[ab].
    (* Goal: eval ?ab = eval [(10,a1);(1,a0)] * eval [(10,b1);(1,b0)] *)
    rewrite <-eval_mul.
    (* Goal: eval ?ab = eval (mul [(10,a1);(1,a0)] [(10,b1);(1,b0)]) *)
    cbv -[Z.mul eval]; cbn -[eval].
    (* Goal: eval ?ab = eval [(100,(a1*b1));(10,a1*b0);(10,a0*b1);(1,a0*b0)]%RT *)
    trivial.                                              Defined.

  Lemma eval_partition f (p:list (Z*Z)) :
    eval (snd (partition f p)) + eval (fst (partition f p)) = eval p.
  Proof. induction p; cbn [partition]; eta_expand; break_match; cbn [fst snd]; push; nsatz. Qed.
  Hint Rewrite eval_partition : push_eval.

  Lemma eval_partition' f (p:list (Z*Z)) :
    eval (fst (partition f p)) + eval (snd (partition f p)) = eval p.
  Proof. rewrite Z.add_comm, eval_partition; reflexivity. Qed.
  Hint Rewrite eval_partition' : push_eval.

  Lemma eval_fst_partition f p : eval (fst (partition f p)) = eval p - eval (snd (partition f p)).
  Proof. rewrite <- (eval_partition f p); nsatz. Qed.
  Lemma eval_snd_partition f p : eval (snd (partition f p)) = eval p - eval (fst (partition f p)).
  Proof. rewrite <- (eval_partition f p); nsatz. Qed.

  Definition split (s:Z) (p:list (Z*Z)) : list (Z*Z) * list (Z*Z)
    := let hi_lo := partition (fun t => fst t mod s =? 0) p in
       (snd hi_lo, map (fun t => (fst t / s, snd t)) (fst hi_lo)).
  Lemma eval_snd_split s p (s_nz:s<>0) :
    s * eval (snd (split s p)) = eval (fst (partition (fun t => fst t mod s =? 0) p)).
  Proof using Type. cbv [split Let_In]; induction p;
    repeat match goal with
    | |- context[?a/?b] =>
      unique pose proof (Z_div_exact_full_2 a b ltac:(trivial) ltac:(trivial))
    | _ => progress push
    | _ => progress break_match
    | _ => progress nsatz                                end. Qed.
  Lemma eval_split s p (s_nz:s<>0) :
    eval (fst (split s p)) + s * eval (snd (split s p)) = eval p.
  Proof using Type. rewrite eval_snd_split, eval_fst_partition by assumption; cbv [split Let_In]; cbn [fst snd]; lia. Qed.

  Lemma reduction_rule' b s c (modulus_nz:s-c<>0) :
    (s * b) mod (s - c) = (c * b) mod (s - c).
  Proof using Type. replace (s * b) with ((c*b) + b*(s-c)) by nsatz.
    rewrite Z.add_mod,Z_mod_mult,Z.add_0_r,Z.mod_mod;trivial. Qed.

  Lemma reduction_rule a b s c (modulus_nz:s-c<>0) :
    (a + s * b) mod (s - c) = (a + c * b) mod (s - c).
  Proof using Type. apply Z.add_mod_Proper; [ reflexivity | apply reduction_rule', modulus_nz ]. Qed.

  Definition reduce (s:Z) (c:list _) (p:list _) : list (Z*Z) :=
    let lo_hi := split s p in fst lo_hi ++ mul c (snd lo_hi).

  Lemma eval_reduce s c p (s_nz:s<>0) (modulus_nz:s-eval c<>0) :
    eval (reduce s c p) mod (s - eval c) = eval p mod (s - eval c).
  Proof using Type. cbv [reduce]; push.
         rewrite <-reduction_rule, eval_split; trivial.      Qed.
  Hint Rewrite eval_reduce : push_eval.

  Lemma eval_reduce_adjusted s c p w c' (s_nz:s<>0) (modulus_nz:s-eval c<>0)
        (w_mod:w mod s = 0) (w_nz:w <> 0) (Hc' : eval c' = (w / s) * eval c) :
    eval (reduce w c' p) mod (s - eval c) = eval p mod (s - eval c).
  Proof using Type.
    cbv [reduce]; push.
    rewrite Hc', <- (Z.mul_comm (eval c)), <- !Z.mul_assoc, <-reduction_rule by auto.
    autorewrite with zsimplify_const; rewrite !Z.mul_assoc, Z.mul_div_eq_full, w_mod by auto.
    autorewrite with zsimplify_const; rewrite eval_split; trivial.
  Qed.

  (* reduce at most [n] times, stopping early if the high list is nil at any point *)
  Definition repeat_reduce (n : nat) (s:Z) (c:list _) (p:list _) : list (Z * Z)
    := nat_rect
         _
         (fun p => p)
         (fun n' repeat_reduce_n' p
          => let lo_hi := split s p in
             if (length (snd lo_hi) =? 0)%nat
             then p
             else let p := fst lo_hi ++ mul c (snd lo_hi) in
                  repeat_reduce_n' p)
         n
         p.

  Lemma repeat_reduce_S_step n s c p
    : repeat_reduce (S n) s c p
      = if (length (snd (split s p)) =? 0)%nat
        then p
        else repeat_reduce n s c (reduce s c p).
  Proof using Type. cbv [repeat_reduce]; cbn [nat_rect]; break_innermost_match; auto. Qed.

  Lemma eval_repeat_reduce n s c p (s_nz:s<>0) (modulus_nz:s-eval c<>0) :
    eval (repeat_reduce n s c p) mod (s - eval c) = eval p mod (s - eval c).
  Proof using Type.
    revert p; induction n as [|n IHn]; intro p; [ reflexivity | ];
      rewrite repeat_reduce_S_step; break_innermost_match;
        [ reflexivity | rewrite IHn ].
    now rewrite eval_reduce.
  Qed.
  Hint Rewrite eval_repeat_reduce : push_eval.

  Lemma eval_repeat_reduce_adjusted n s c p w c' (s_nz:s<>0) (modulus_nz:s-eval c<>0)
        (w_mod:w mod s = 0) (w_nz:w <> 0) (Hc' : eval c' = (w / s) * eval c) :
    eval (repeat_reduce n w c' p) mod (s - eval c) = eval p mod (s - eval c).
  Proof using Type.
    revert p; induction n as [|n IHn]; intro p; [ reflexivity | ];
      rewrite repeat_reduce_S_step; break_innermost_match;
        [ reflexivity | rewrite IHn ].
    now rewrite eval_reduce_adjusted.
  Qed.

  (*
  Definition splitQ (s:Q) (p:list (Z*Z)) : list (Z*Z) * list (Z*Z)
    := let hi_lo := partition (fun t => (fst t * Zpos (Qden s)) mod (Qnum s) =? 0) p in
       (snd hi_lo, map (fun t => ((fst t * Zpos (Qden s)) / Qnum s, snd t)) (fst hi_lo)).
  Lemma eval_snd_splitQ s p (s_nz:Qnum s<>0) :
   Qnum s * eval (snd (splitQ s p)) = eval (fst (partition (fun t => (fst t * Zpos (Qden s)) mod (Qnum s) =? 0) p)) * Zpos (Qden s).
  Proof using Type.
    (* Work around https://github.com/mit-plv/fiat-crypto/issues/381 ([nsatz] can't handle [Zpos]) *)
    cbv [splitQ Let_In]; cbn [fst snd]; zify; generalize dependent (Zpos (Qden s)); generalize dependent (Qnum s); clear s; intros.
    induction p;
    repeat match goal with
    | |- context[?a/?b] =>
      unique pose proof (Z_div_exact_full_2 a b ltac:(trivial) ltac:(trivial))
    | _ => progress push
    | _ => progress break_match
    | _ => progress nsatz                                end. Qed.
  Lemma eval_splitQ s p (s_nz:Qnum s<>0) :
    eval (fst (splitQ s p)) + (Qnum s * eval (snd (splitQ s p))) / Zpos (Qden s) = eval p.
  Proof using Type. rewrite eval_snd_splitQ, eval_fst_partition by assumption; cbv [splitQ Let_In]; cbn [fst snd]; Z.div_mod_to_quot_rem_in_goal; nia. Qed.
  Lemma eval_splitQ_mul s p (s_nz:Qnum s<>0) :
    eval (fst (splitQ s p)) * Zpos (Qden s) + (Qnum s * eval (snd (splitQ s p))) = eval p * Zpos (Qden s).
  Proof using Type. rewrite eval_snd_splitQ, eval_fst_partition by assumption; cbv [splitQ Let_In]; cbn [fst snd]; nia. Qed.
   *)
  Lemma eval_rev p : eval (rev p) = eval p.
  Proof using Type. induction p; cbn [rev]; push; lia. Qed.
  Hint Rewrite eval_rev : push_eval.
  (*
  Lemma eval_permutation (p q : list (Z * Z)) : Permutation p q -> eval p = eval q.
  Proof using Type. induction 1; push; nsatz.                          Qed.

  Module RevWeightOrder <: TotalLeBool.
    Definition t := (Z * Z)%type.
    Definition leb (x y : t) := Z.leb (fst y) (fst x).
    Infix "<=?" := leb.
    Local Coercion is_true : bool >-> Sortclass.
    Theorem leb_total : forall a1 a2, a1 <=? a2 \/ a2 <=? a1.
    Proof using Type.
      cbv [is_true leb]; intros x y; rewrite !Z.leb_le; pose proof (Z.le_ge_cases (fst x) (fst y)).
      lia.
    Qed.
    Global Instance leb_Transitive : Transitive leb.
    Proof using Type. repeat intro; unfold is_true, leb in *; Z.ltb_to_lt; lia. Qed.
  End RevWeightOrder.

  Module RevWeightSort := Mergesort.Sort RevWeightOrder.

  Lemma eval_sort p : eval (RevWeightSort.sort p) = eval p.
  Proof using Type. symmetry; apply eval_permutation, RevWeightSort.Permuted_sort. Qed.
  Hint Rewrite eval_sort : push_eval.
  *)
  (* rough template (we actually have to do things a bit differently to account for duplicate weights):
[ dlet fi_c := c * fi in
   let (fj_high, fj_low) := split fj at s/fi.weight in
   dlet fi_2 := 2 * fi in
    dlet fi_2_c := 2 * fi_c in
    (if fi.weight^2 >= s then fi_c * fi else fi * fi)
       ++ fi_2_c * fj_high
       ++ fi_2 * fj_low
 | fi <- f , fj := (f weight less than i) ]
   *)
  (** N.B. We take advantage of dead code elimination to allow us to
      let-bind partial products that we don't end up using *)
  (** [v] -> [(v, v*c, v*c*2, v*2)] *)
  Definition let_bind_for_reduce_square (c:list (Z*Z)) (p:list (Z*Z)) : list ((Z*Z) * list(Z*Z) * list(Z*Z) * list(Z*Z)) :=
    let two := [(1,2)] (* (weight, value) *) in
    map (fun t => dlet c_t := mul [t] c in dlet two_c_t := mul c_t two in dlet two_t := mul [t] two in (t, c_t, two_c_t, two_t)) p.
  Definition reduce_square (s:Z) (c:list (Z*Z)) (p:list (Z*Z)) : list (Z*Z) :=
    let p := let_bind_for_reduce_square c p in
    let div_s := map (fun t => (fst t / s, snd t)) in
    list_rect
      _
      nil
      (fun t ts acc
       => (let '(t, c_t, two_c_t, two_t) := t in
           (if ((fst t * fst t) mod s =? 0)
            then div_s (mul [t] c_t)
            else mul [t] [t])
             ++ (flat_map
                   (fun '(t', c_t', two_c_t', two_t')
                    => if ((fst t * fst t') mod s =? 0)
                       then div_s
                              (if fst t' <=? fst t
                               then mul [t'] two_c_t
                               else mul [t] two_c_t')
                       else (if fst t' <=? fst t
                             then mul [t'] two_t
                             else mul [t] two_t'))
                   ts))
            ++ acc)
      p.
  Lemma eval_map_div s p (s_nz:s <> 0) (Hmod : forall v, In v p -> fst v mod s = 0)
    : eval (map (fun x => (fst x / s, snd x)) p) = eval p / s.
  Proof using Type.
    assert (Hmod' : forall v, In v p -> (fst v * snd v) mod s = 0).
    { intros; push_Zmod; rewrite Hmod by assumption; autorewrite with zsimplify_const; reflexivity. }
    induction p as [|p ps IHps]; push.
    { autorewrite with zsimplify_const; reflexivity. }
    { cbn [In] in *; rewrite Z.div_add_exact by eauto.
      rewrite !Z.Z_divide_div_mul_exact', IHps by auto using Znumtheory.Zmod_divide.
      nsatz. }
  Qed.
  Lemma eval_map_mul_div s a b c (s_nz:s <> 0) (a_mod : (a*a) mod s = 0)
    : eval (map (fun x => ((a * (a * fst x)) / s, b * (b * snd x))) c) = ((a * a) / s) * (b * b) * eval c.
  Proof using Type.
    rewrite <- eval_map_mul; apply f_equal, map_ext; intro.
    rewrite !Z.mul_assoc.
    rewrite !Z.Z_divide_div_mul_exact' by auto using Znumtheory.Zmod_divide.
    f_equal; nia.
  Qed.
  Hint Rewrite eval_map_mul_div using solve [ auto ] : push_eval.

  Lemma eval_map_mul_div' s a b c (s_nz:s <> 0) (a_mod : (a*a) mod s = 0)
    : eval (map (fun x => (((a * a) * fst x) / s, (b * b) * snd x)) c) = ((a * a) / s) * (b * b) * eval c.
  Proof using Type. rewrite <- eval_map_mul_div by assumption; f_equal; apply map_ext; intro; Z.div_mod_to_quot_rem_in_goal; f_equal; nia. Qed.
  Hint Rewrite eval_map_mul_div' using solve [ auto ] : push_eval.

  Lemma eval_flat_map_if A (f : A -> bool) g h p
    : eval (flat_map (fun x => if f x then g x else h x) p)
      = eval (flat_map g (fst (partition f p))) + eval (flat_map h (snd (partition f p))).
  Proof using Type.
    induction p; cbn [flat_map partition fst snd]; eta_expand; break_match; cbn [fst snd]; push;
      nsatz.
  Qed.
  (*Local Hint Rewrite eval_flat_map_if : push_eval.*) (* this should be [Local], but that doesn't work *)

  Lemma eval_if (b : bool) p q : eval (if b then p else q) = if b then eval p else eval q.
  Proof using Type. case b; reflexivity. Qed.
  Hint Rewrite eval_if : push_eval.

  Lemma split_app s p q :
    split s (p ++ q) = (fst (split s p) ++ fst (split s q), snd (split s p) ++ snd (split s q)).
  Proof using Type.
    cbv [split]; rewrite !partition_app; cbn [fst snd].
    rewrite !map_app; reflexivity.
  Qed.
  Lemma fst_split_app s p q :
    fst (split s (p ++ q)) = fst (split s p) ++ fst (split s q).
  Proof using Type. rewrite split_app; reflexivity. Qed.
  Lemma snd_split_app s p q :
    snd (split s (p ++ q)) = snd (split s p) ++ snd (split s q).
  Proof using Type. rewrite split_app; reflexivity. Qed.
  Hint Rewrite fst_split_app snd_split_app : push_eval.

  Lemma eval_reduce_list_rect_app A s c N C p :
    eval (reduce s c (@list_rect A _ N (fun x xs acc => C x xs ++ acc) p))
    = eval (@list_rect A _ (reduce s c N) (fun x xs acc => reduce s c (C x xs) ++ acc) p).
  Proof using Type.
    cbv [reduce]; induction p as [|p ps IHps]; cbn [list_rect]; push; [ nsatz | rewrite <- IHps; clear IHps ].
    push; nsatz.
  Qed.
  Hint Rewrite eval_reduce_list_rect_app : push_eval.

  Lemma eval_list_rect_app A N C p :
    eval (@list_rect A _ N (fun x xs acc => C x xs ++ acc) p)
    = @list_rect A _ (eval N) (fun x xs acc => eval (C x xs) + acc) p.
  Proof using Type. induction p; cbn [list_rect]; push; nsatz. Qed.
  Hint Rewrite eval_list_rect_app : push_eval.

  Local Existing Instances list_rect_Proper pointwise_map flat_map_Proper.
  Local Hint Extern 0 (Proper _ _) => solve_Proper_eq : typeclass_instances.

  Lemma reduce_nil s c : reduce s c nil = nil.
  Proof using Type. cbv [reduce]; induction c; cbn; intuition auto. Qed.
  Hint Rewrite reduce_nil : push_eval.

  Lemma eval_reduce_app s c p q : eval (reduce s c (p ++ q)) = eval (reduce s c p) + eval (reduce s c q).
  Proof using Type. cbv [reduce]; push; nsatz. Qed.
  Hint Rewrite eval_reduce_app : push_eval.

  Lemma eval_reduce_cons s c p q :
    eval (reduce s c (p :: q))
    = (if fst p mod s =? 0 then eval c * ((fst p / s) * snd p) else fst p * snd p)
      + eval (reduce s c q).
  Proof using Type.
    cbv [reduce split]; cbn [partition fst snd]; eta_expand; push.
    break_innermost_match; cbn [fst snd map]; push; nsatz.
  Qed.
  Hint Rewrite eval_reduce_cons : push_eval.

  Lemma mul_cons_l t ts p :
    mul (t::ts) p = map (fun t' => (fst t * fst t', snd t * snd t')) p ++ mul ts p.
  Proof using Type. reflexivity. Qed.
  Lemma mul_nil_l p : mul nil p = nil.
  Proof using Type. reflexivity. Qed.
  Lemma mul_nil_r p : mul p nil = nil.
  Proof using Type. cbv [mul]; induction p; cbn; intuition auto. Qed.
  Hint Rewrite mul_nil_l mul_nil_r : push_eval.
  Lemma mul_app_l p p' q :
    mul (p ++ p') q = mul p q ++ mul p' q.
  Proof using Type. cbv [mul]; rewrite flat_map_app; reflexivity. Qed.
  Lemma mul_singleton_l_app_r p q q' :
    mul [p] (q ++ q') = mul [p] q ++ mul [p] q'.
  Proof using Type. cbv [mul flat_map]; rewrite !map_app, !app_nil_r; reflexivity. Qed.
  Hint Rewrite mul_singleton_l_app_r : push_eval.
  Lemma mul_singleton_singleton p q :
    mul [p] [q] = [(fst p * fst q, snd p * snd q)].
  Proof using Type. reflexivity. Qed.

  Lemma eval_reduce_square_step_helper s c t' t v (s_nz:s <> 0) :
    (fst t * fst t') mod s = 0 \/ (fst t' * fst t) mod s = 0 -> In v (mul [t'] (mul (mul [t] c) [(1, 2)])) -> fst v mod s = 0.
  Proof using Type.
    cbv [mul]; cbn [map flat_map fst snd].
    rewrite !app_nil_r, flat_map_singleton, !map_map; cbn [fst snd]; rewrite in_map_iff; intros [H|H] [? [? ?] ]; subst; revert H.
    all:cbn [fst snd]; autorewrite with zsimplify_const; intro H; rewrite Z.mul_assoc, Z.mul_mod_l.
    all:rewrite H || rewrite (Z.mul_comm (fst t')), H; autorewrite with zsimplify_const; reflexivity.
  Qed.

  Lemma eval_reduce_square_step s c t ts (s_nz : s <> 0) :
    eval (flat_map
            (fun t' => if (fst t * fst t') mod s =? 0
                    then map (fun t => (fst t / s, snd t))
                             (if fst t' <=? fst t
                              then mul [t'] (mul (mul [t] c) [(1, 2)])
                              else mul [t] (mul (mul [t'] c) [(1, 2)]))
                    else (if fst t' <=? fst t
                          then mul [t'] (mul [t] [(1, 2)])
                          else mul [t] (mul [t'] [(1, 2)])))
            ts)
    = eval (reduce s c (mul [(1, 2)] (mul [t] ts))).
  Proof using Type.
    induction ts as [|t' ts IHts]; cbn [flat_map]; [ push; nsatz | rewrite eval_app, IHts; clear IHts ].
    change (t'::ts) with ([t'] ++ ts); rewrite !mul_singleton_l_app_r, !mul_singleton_singleton; autorewrite with zsimplify_const; push.
    break_match; Z.ltb_to_lt; push; try nsatz.
    all:rewrite eval_map_div by eauto using eval_reduce_square_step_helper; push; autorewrite with zsimplify_const.
    all:rewrite ?Z.mul_assoc, <- !(Z.mul_comm (fst t')), ?Z.mul_assoc.
    all:rewrite ?Z.mul_assoc, <- !(Z.mul_comm (fst t)), ?Z.mul_assoc.
    all:rewrite <- !Z.mul_assoc, Z.mul_assoc.
    all:rewrite !Z.Z_divide_div_mul_exact' by auto using Znumtheory.Zmod_divide.
    all:nsatz.
  Qed.

  Lemma eval_reduce_square_helper s c x y v (s_nz:s <> 0) :
    (fst x * fst y) mod s = 0 \/ (fst y * fst x) mod s = 0 -> In v (mul [x] (mul [y] c)) -> fst v mod s = 0.
  Proof using Type.
    cbv [mul]; cbn [map flat_map fst snd].
    rewrite !app_nil_r, ?flat_map_singleton, !map_map; cbn [fst snd]; rewrite in_map_iff; intros [H|H] [? [? ?] ]; subst; revert H.
    all:cbn [fst snd]; autorewrite with zsimplify_const; intro H; rewrite Z.mul_assoc, Z.mul_mod_l.
    all:rewrite H || rewrite (Z.mul_comm (fst x)), H; autorewrite with zsimplify_const; reflexivity.
  Qed.

  Lemma eval_reduce_square_exact s c p (s_nz:s<>0) (modulus_nz:s-eval c<>0)
    : eval (reduce_square s c p) = eval (reduce s c (square p)).
  Proof using Type.
    cbv [let_bind_for_reduce_square reduce_square square Let_In]; rewrite list_rect_map; push.
    apply list_rect_Proper; [ | repeat intro; subst | reflexivity ]; cbv [split]; push; [ nsatz | ].
    rewrite flat_map_map, eval_reduce_square_step by auto.
    break_match; Z.ltb_to_lt; push.
    1:rewrite eval_map_div by eauto using eval_reduce_square_helper; push.
    all:cbv [mul]; cbn [map flat_map fst snd]; rewrite !app_nil_r, !map_map; cbn [fst snd].
    all:autorewrite with zsimplify_const.
    all:rewrite <- ?Z.mul_assoc, !(Z.mul_comm (fst a)), <- ?Z.mul_assoc.
    all:rewrite ?Z.mul_assoc, <- (Z.mul_assoc _ (fst a) (fst a)), <- !(Z.mul_comm (fst a * fst a)).
    1:rewrite !Z.Z_divide_div_mul_exact' by auto using Znumtheory.Zmod_divide.
    all:idtac;
      let LHS := match goal with |- ?LHS = ?RHS => LHS end in
      let RHS := match goal with |- ?LHS = ?RHS => RHS end in
      let f := match LHS with context[eval (reduce _ _ (map ?f _))] => f end in
      let g := match RHS with context[eval (reduce _ _ (map ?f _))] => f end in
      rewrite (map_ext f g) by (intros; f_equal; nsatz).
    all:nsatz.
  Qed.
  Lemma eval_reduce_square s c p (s_nz:s<>0) (modulus_nz:s-eval c<>0)
    : eval (reduce_square s c p) mod (s - eval c)
      = (eval p * eval p) mod (s - eval c).
  Proof using Type. rewrite eval_reduce_square_exact by assumption; push; auto. Qed.
  Hint Rewrite eval_reduce_square : push_eval.

  Definition bind_snd (p : list (Z*Z)) :=
    map (fun t => dlet_nd t2 := snd t in (fst t, t2)) p.

  Lemma bind_snd_correct p : bind_snd p = p.
  Proof using Type.
    cbv [bind_snd]; induction p as [| [? ?] ];
      push; [|rewrite IHp]; reflexivity.
  Qed.

  Section Carries.
    Definition carryterm (w fw:Z) (t:Z * Z) :=
      if (Z.eqb (fst t) w)
      then dlet_nd t2 := snd t in
           dlet_nd d2 := t2 / fw in
           dlet_nd m2 := t2 mod fw in
           [(w * fw, d2);(w,m2)]
      else [t].

    Lemma eval_carryterm w fw (t:Z * Z) (fw_nonzero:fw<>0):
      eval (carryterm w fw t) = eval [t].
    Proof using Type*.
      cbv [carryterm Let_In]; break_match; push; [|trivial].
      pose proof (Z.div_mod (snd t) fw fw_nonzero).
      rewrite Z.eqb_eq in *.
      nsatz.
    Qed. Hint Rewrite eval_carryterm using auto : push_eval.

    Definition carry (w fw:Z) (p:list (Z * Z)):=
      flat_map (carryterm w fw) p.

    Lemma eval_carry w fw p (fw_nonzero:fw<>0):
      eval (carry w fw p) = eval p.
    Proof using Type*. cbv [carry]; induction p; push; nsatz. Qed.
    Hint Rewrite eval_carry using auto : push_eval.
  End Carries.
End Associational.
