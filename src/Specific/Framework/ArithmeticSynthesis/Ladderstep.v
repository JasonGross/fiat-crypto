Require Import Coq.ZArith.BinIntDef.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Curves.Montgomery.XZ.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.HelperTactics.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Tactics.PoseTermWithName.
Require Import Crypto.Util.Tactics.CacheTerm.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Notations.

Local Notation tuple := Tuple.tuple.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Infix "^" := tuple : type_scope.

(** TODO(jadep,andreser): Move to NewBaseSystemTest? *)
Definition FMxzladderstep {m} := @M.donnaladderstep (F m) F.add F.sub F.mul.

Section with_notations.
  Context (T_tight T_loose retT : Type).
  Local Notation preretT := (tuple (tuple T_tight 2) 2).
  Context (relax : T_tight -> T_loose)
          (let_inT : T_tight -> (T_tight -> retT) -> retT)
          (let_inL : T_loose -> (T_loose -> retT) -> retT)
          (add sub : T_tight -> T_tight -> T_loose)
          (carry_mul : T_loose -> T_loose -> T_tight)
          (carry_square : T_loose -> T_tight)
          (cont : preretT -> retT).
  Local Infix "+" := add.
  Local Notation "a * b" := (carry_mul a b).
  Local Notation "x ^ 2" := (carry_square x).
  Local Infix "-" := sub.
  Local Notation "'dlet' x .. y := v 'in' f" := (let_inT v (fun x => .. (fun y => f) .. )).
  Local Notation "'llet' x := v 'in' f" := (let_inL v (fun x => f)).
  Local Coercion relax : T_tight >-> T_loose.
  Definition Mxzladderstep_cps a24 x1 Q Q'
    := match Q, Q' with
       | (x, z), (x', z') =>
         dlet origx := x in
         llet x := x + z in
         llet z := origx - z in
         dlet origx' := x' in
         llet x' := x' + z' in
         llet z' := origx' - z' in
         dlet xx' := x' * z in
         dlet zz' := x * z' in
         dlet origx' := xx' in
         llet xx' := xx' + zz' in
         llet zz' := origx' - zz' in
         dlet x3 := xx'^2 in
         dlet zzz' := zz'^2 in
         dlet z3 := zzz' * x1 in
         dlet xx := x^2 in
         dlet zz := z^2 in
         dlet x2 := xx * zz in
         llet zz := xx - zz in
         dlet zzz := zz * a24 in
         llet zzz := zzz + xx in
         dlet z2 := zz * zzz in
         cont ((x2, z2), (x3, z3))%core
       end.


  Lemma Mxzladderstep_cps_Proper1
        (P_tight : T_tight -> Prop)
        (P_loose : T_loose -> Prop)
        (P_ret : retT -> Prop)
        (P_preret : tuple (tuple T_tight 2) 2 -> Prop
         := fun x => (P_tight (fst (fst x)) /\ P_tight (snd (fst x)))
                     /\ (P_tight (fst (snd x)) /\ P_tight (snd (snd x))))
        (P_relax : forall x, P_tight x -> P_loose (relax x))
        (P_let_inT : forall x (_ : P_tight x) f (_ : forall x, P_tight x -> P_ret (f x)), P_ret (let_inT x f))
        (P_let_inL : forall x (_ : P_loose x) f (_ : forall x, P_loose x -> P_ret (f x)), P_ret (let_inL x f))
        (P_add : forall x (_ : P_tight x) y (_ : P_tight y), P_loose (add x y))
        (P_sub : forall x (_ : P_tight x) y (_ : P_tight y), P_loose (sub x y))
        (P_carry_mul : forall x (_ : P_loose x) y (_ : P_loose y), P_tight (carry_mul x y))
        (P_carry_square : forall x (_ : P_loose x), P_tight (carry_square x))
        (P_cont : forall x (_ : P_preret x), P_ret (cont x))
        a24 x1 Q Q'
        (P_a24 : P_loose a24)
        (P_x1 : P_loose x1)
        (P_Q : P_tight (fst Q) /\ P_tight (snd Q))
        (P_Q' : P_tight (fst Q') /\ P_tight (snd Q'))
    : P_ret (Mxzladderstep_cps a24 x1 Q Q').
  Proof.
    destruct Q, Q', P_Q, P_Q'; cbv [Mxzladderstep_cps]; cbn [fst snd] in *.
    repeat match goal with
           | [ H : _ |- _ ] => apply H; repeat intro; try assumption
           | _ => progress repeat apply conj; try assumption
           end.
  Qed.
End with_notations.

Section hetero.
  Local Notation "f ==> g"
    := (respectful_hetero _ _ (fun _ => _) (fun _ => _) f%signature (fun _ _ => g%signature)) : signature_scope.
  Local Notation "R ^ n" := (Tuple.fieldwise (n:=n%nat) R%signature) : signature_scope.
  Local Notation "R ^ 2" := (Tuple.fieldwise (n:=2) R%signature) : signature_scope.

  Lemma Mxzladderstep_cps_Proper_hetero
        {T1_tight T1_loose T2_tight T2_loose retT1 retT2}
        (R_tight : T1_tight -> T2_tight -> Prop)
        (R_loose : T1_loose -> T2_loose -> Prop)
        (R_retT : retT1 -> retT2 -> Prop)
    : (((R_tight ==> R_loose)
          ==> (R_tight ==> (R_tight ==> R_retT) ==> R_retT)
          ==> (R_loose ==> (R_loose ==> R_retT) ==> R_retT)
          ==> (R_tight ==> R_tight ==> R_loose)
          ==> (R_tight ==> R_tight ==> R_loose)
          ==> (R_loose ==> R_loose ==> R_tight)
          ==> (R_loose ==> R_tight)
          ==> ((R_tight^2)^2 ==> R_retT)
          ==> R_loose
          ==> R_loose
          ==> (R_tight^2)
          ==> (R_tight^2)
          ==> R_retT)%signature)
        (@Mxzladderstep_cps T1_tight T1_loose retT1)
        (@Mxzladderstep_cps T2_tight T2_loose retT2).
  Proof.
    cbv [tuple tuple']; repeat intro; destruct_head'_prod;
      destruct_head_hnf' and;
      cbn [fst snd] in *; cbv [fieldwise'] in *.
    cbv [Mxzladderstep_cps].
    repeat match goal with
           | _ => progress repeat intro
           | [ H : _ |- _ ] => apply H; try assumption
           | _ => progress repeat apply conj; cbn [fst snd]; try assumption
           end.
  Qed.
End hetero.

Lemma Mxzladderstep_id_gen
      (T_tight T_loose retT : Type)
      (preretT := (tuple (tuple T_tight 2) 2))
      (relax : T_tight -> T_loose)
      (let_inT : T_tight -> (T_tight -> retT) -> retT)
      (let_inL : T_loose -> (T_loose -> retT) -> retT)
      (add sub : T_tight -> T_tight -> T_loose)
      (carry_mul : T_loose -> T_loose -> T_tight)
      (carry_square : T_loose -> T_tight)
      (cont : preretT -> retT)
      (let_inT' : T_tight -> (T_tight -> preretT) -> preretT)
      (let_inL' : T_loose -> (T_loose -> preretT) -> preretT)
      (eval_let_inT : forall x f, let_inT x f = f x)
      (eval_let_inL : forall x f, let_inL x f = f x)
      (eval_let_inT' : forall x f, let_inT' x f = f x)
      (eval_let_inL' : forall x f, let_inL' x f = f x)
      a24 x1 Q Q'
  : @Mxzladderstep_cps T_tight T_loose retT relax let_inT let_inL add sub carry_mul carry_square cont a24 x1 Q Q'
    = cont (@Mxzladderstep_cps T_tight T_loose _ relax let_inT' let_inL' add sub carry_mul carry_square id a24 x1 Q Q').
Proof.
  destruct Q, Q'; cbv [Mxzladderstep_cps];
    repeat rewrite ?eval_let_inT, ?eval_let_inT', ?eval_let_inL, ?eval_let_inL'; reflexivity.
Qed.

Definition FMxzladderstep_Mxzladderstep_cps_id {m}
  : @FMxzladderstep m
    = @Mxzladderstep_cps (F m) (F m) _ id (@Let_In _ (fun _ => _)) (@Let_In _ (fun _ => _)) F.add F.sub F.mul (fun x => F.mul x x) id
  := eq_refl.


(*

Ltac pose_a24' a24 a24' :=
  let a24 := (eval vm_compute in (invert_Some a24)) in
  cache_term_with_type_by
    Z
    ltac:(exact a24)
           a24'.

Ltac pose_a24_sig sz m wt a24' a24_sig :=
  cache_term_with_type_by
    { a24t : Z^sz | Positional.Fdecode (m:=m) wt a24t = F.of_Z m a24' }
    solve_constant_sig
    a24_sig.

Ltac pose_Mxzladderstep_sig sz wt m add_sig sub_sig mul_sig square_sig carry_sig Mxzladderstep_sig :=
  cache_term_with_type_by
    { xzladderstep : tuple Z sz -> tuple Z sz -> tuple Z sz * tuple Z sz -> tuple Z sz * tuple Z sz -> tuple Z sz * tuple Z sz * (tuple Z sz * tuple Z sz)
    | forall a24 x1 Q Q', let eval := B.Positional.Fdecode wt in Tuple.map (n:=2) (Tuple.map (n:=2) eval) (xzladderstep a24 x1 Q Q') = FMxzladderstep (m:=m) (eval a24) (eval x1) (Tuple.map (n:=2) eval Q) (Tuple.map (n:=2) eval Q') }
    ltac:((exists (Mxzladderstep sz (proj1_sig add_sig) (proj1_sig sub_sig) (proj1_sig mul_sig) (proj1_sig square_sig) (proj1_sig carry_sig)));
          let a24 := fresh "a24" in
          let x1 := fresh "x1" in
          let Q := fresh "Q" in
          let Q' := fresh "Q'" in
          let eval := fresh "eval" in
          intros a24 x1 Q Q' eval;
          cbv [Mxzladderstep FMxzladderstep M.donnaladderstep];
          destruct Q, Q'; cbv [map map' fst snd Let_In eval];
          repeat match goal with
                 | [ |- context[@proj1_sig ?a ?b ?s] ]
                   => rewrite !(@proj2_sig a b s)
                 end;
          reflexivity)
           Mxzladderstep_sig.
*)
