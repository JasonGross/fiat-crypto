Require Import Coq.Classes.Morphisms Coq.Relations.Relation_Definitions.
Require Import Crypto.Util.Tactics.

Definition Let_In {A P} (x : A) (f : forall a : A, P a) : P x := let y := x in f y.

Global Instance Proper_Let_In_changebody {A P R} {Reflexive_R:@Reflexive P R}
  : Proper (eq ==> pointwise_relation _ R ==> R) (@Let_In A (fun _ => P)).
Proof. lazy; intros; subst; auto; congruence. Qed.

Global Instance Proper_Let_In_changevalue {A B} RA {RB} (f:A->B) {Proper_f:Proper (RA==>RB) f}
  : Proper (RA ==> RB) (fun x => Let_In x f).
Proof. intuition. Qed.

Ltac change_let_in_with_Let_In :=
  match goal with
  | [ |- context G[let x := ?y in @?z x] ]
    => let G' := context G[Let_In y z] in change G'
  end.

Lemma Let_In_changebody_lem {V T} {R:relation T} (f g:V->T) :
  (forall x, R (f x) (g x)) -> forall v, R (Let_In v f) (Let_In v g).
Proof. trivial. Qed.
Ltac Let_In_changebody :=
  match goal with
    |- ?R ?LHS (Let_In ?v ?f)
    =>
    (* set variables before [eapply] because both [eapply] and
      [refine] reduce a match that is applied to a constructor *)
    (* TODO: make a coq issue for this *)
    let ff := fresh "ff" in 
    let vv := fresh "vv" in 
    set (ff := f); set (vv := v);
    eapply Let_In_changebody_lem;
    intro;
    subst ff; subst vv; cbv beta (* FUTURE: don't do reduction elsewhere *)
  end.

Ltac let_in_changebody :=
  change_let_in_with_Let_In;
  Let_In_changebody;
  cbv beta delta [Let_In]. (* FUTURE: don't do reduction elsewhere *)

Ltac recursive_change_let_in_with_Let_In :=
  change_let_in_with_Let_In;
  etransitivity; [|Let_In_changebody; try recursive_change_let_in_with_Let_In; reflexivity].

Ltac change_Let_app_In_with_Let_In_app fn :=
  match goal with
  | [ |- appcontext G[Let_In (fn ?x) ?f] ]
    => change (Let_In (fn x) f) with (Let_In x (fun y => f (fn y))); cbv beta
  end.

Lemma Let_app_In_Let_In_app {A B T} (g:A->B) (f:B->T) (x:A) :
    @Let_In _ (fun _ => T) (g x) f =
    @Let_In _ (fun _ => T) x (fun p => f (g x)).
Proof. reflexivity. Qed.

Lemma Let_In_app_app_Let_In {B C} (f : B -> C) A (v : A) (b : A -> B)
  : Let_In v (fun v' => f (b v')) = f (Let_In v b).
Proof.
  reflexivity.
Qed.

Ltac let_nonvariables_before_match_pair :=
  match goal with
  | |- ?R ?LHS match pair ?a ?b with pair e f => @?P e f end
    => not is_var a; not is_var b; change (R LHS (let xa := a in let xb := b in match pair xa xb with pair e f => P e f end))
  | |- ?R ?LHS match pair ?a ?b with pair e f => @?P e f end
    => not is_var b; change (R LHS (let xb := b in match pair a xb with pair e f => P e f end))
  | |- ?R ?LHS match pair ?a ?b with pair e f => @?P e f end
    => not is_var a; change (R LHS (let xa := a in match pair xa b with pair e f => P e f end))
  end;
  cbv beta. (* FUTURE: do not reduce elsewhere *)

Ltac replace_match_let_in_pair_with_let_in_match_pair_step :=
  match goal with
    |- ?R ?LHS match (let x := ?E in @?C x) with pair e f => @?P e f end
    =>  let RHS' := eval cbv beta in (let x := E in match C x with pair e f => P e f end) in
            change (R LHS RHS'); let_in_changebody
  
  end.

(* TODO: generalize this to matching on other constructors than pair? *)
Ltac replace_match_let_in_pair_with_let_in_match_pair :=
  etransitivity;
    [|
     repeat replace_match_let_in_pair_with_let_in_match_pair_step;
     let_nonvariables_before_match_pair;
       cbv iota beta; (* FUTURE: do not reduce elsewhere *)
       recursive_change_let_in_with_Let_In; (* KLUDGE: unification to not destroy our let binders *)
     reflexivity
    ];
    cbv beta delta [Let_In].

Goal forall x y z,
    { r | r =
    let '(e, f) := (
          let e := x + y in
          let f := e + z in
          (e+f, e-f)) in
    e + f }.
Proof.
  eexists.
  replace_match_let_in_pair_with_let_in_match_pair.
  
     (*
     match goal with
       |- ?R (?e ?x) ?RHS
       => let RHS' := (eval pattern x in RHS) in
          match RHS' with
            ?f _ => idtac e f; unify e f; idtac e (* FIXME: do not reduce my let binders! *)
          end; cbv beta (* FUTURE: do not beta elsewhere *)
     end.
     *)
     reflexivity.
  } Unfocus. cbv beta delta [Let_In].
  reflexivity.
Qed.

Goal forall
    f0 f1 f2 f3 f4 f5 f6 f7 f8 f9
    g0 g1 g2 g3 g4 g5 g6 g7 g8 g9
    f,
    { r : nat | r =
      let
        '(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9) :=
        let x0 := f0 - g0 in
        let x1 := f1 - g1 in
        let x2 := f2 - g2 in
        let x1 := f1 - g1 in
        let x1 := f1 - g1 in
        let x1 := f1 - g1 in
        let x1 := f1 - g1 in
        let x1 := f1 - g1 in
        let x1 := f1 - g1 in
        let x2 := f2 - g2 in
        let x2 := f2 - g2 in
        let x2 := f2 - g2 in
        let x2 := f2 - g2 in
        let x2 := f2 - g2 in
        let x2 := f2 - g2 in
        let x1 := f1 - g1 in
        let x1 := f1 - g1 in
        let x1 := f1 - g1 in
        let x1 := f1 - g1 in
        let x1 := f1 - g1 in
        let x1 := f1 - g1 in
        let x1 := f1 - g1 in
        let x1 := f1 - g1 in
        let x1 := f1 - g1 in
        let x1 := f1 - g1 in
        let x1 := f1 - g1 in
        let x1 := f1 - g1 in
        let x2 := f2 - g2 in
        let x2 := f2 - g2 in
        let x2 := f2 - g2 in
        let x2 := f2 - g2 in
        let x2 := f2 - g2 in
        let x2 := f2 - g2 in
        let x2 := f2 - g2 in
        let x2 := f2 - g2 in
        let x2 := f2 - g2 in
        let x2 := f2 - g2 in
        let x2 := f2 - g2 in
        let x2 := f2 - g2 in
        ((x0), (x1), (x2), (f3 - g3),
         (f4 - g4), (f5 - g5), (f6 - g6), (f7 - g7),
         (f8 - g8), (f9 - g9)) in
      f a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 }.
Proof.
  eexists.
  replace_match_let_in_pair_with_let_in_match_pair.
  reflexivity.
Qed.

Global Instance Proper_prod_rect_changebody {A B C RC} :
  Proper ((pointwise_relation _ (pointwise_relation _ RC))==>eq==>RC) (@prod_rect A B (fun _ => C)).
Proof.
  repeat intro; repeat match goal with [H:A*B |- _ ] => destruct H end; cbv.
  unfold pointwise_relation in *.
  match goal with [H0:_|-_] =>  injection H0; clear H0; intros; subst; eauto end.
Qed.

(*
Goal forall (P Q : prod nat nat) (a a0:nat),
    0 =
    (let aP := Nat.add a a0 in
     let aP' := Nat.add a0 a in
     match Q with
     | pair xQ yQ => let aQ := Nat.add xQ yQ in
                     let aa := Nat.add aP' aQ in
                     Nat.mul aP aa
     end).

  intros.
  Set Printing All.
  idtac.

  etransitivity;
    [|
    lazymatch goal with
    | |- ?R ?LHS (let x := ?Ex in (match ?v with pair p q => @?C x p q end))
      => is_var x; change (R LHS (match v with pair p q => let x := Ex in (C x p q) end)); cbv beta
    | |- ?R ?LHS (let x := ?Ex in (let y := ?Ey in @?C x y))
      => change_let_in_with_Let_In;
         idtac
    end;
    reflexivity
    ].

  etransitivity;
    [|
     eapply Proper_Let_In_changebody; [reflexivity|]; intro; reflexivity
    ];
    cbv beta delta [Let_In]

    lazymatch goal with
    | |- ?R ?LHS (let x := ?Ex in (match ?v with pair p q => @?C x p q end))
      => is_var x; change (R LHS (match v with pair p q => let x := Ex in (C x p q) end)); cbv beta
    | |- ?R ?LHS (let x := ?Ex in (let y := ?Ey in @?C x y))
      => change_let_in_with_Let_In;
         etransitivity;
         [|
          eapply Proper_Let_In_changebody; [reflexivity|]; intro; reflexivity
         ];
         cbv beta delta [Let_In]
    end.

  (* This passes and does nothing, so the match syntax is fine :) *)
  lazymatch goal with
    |- context [match ?v with pair x y => _ end]
    => is_var v; unify v Q
  end.

  (* this does not work because E contains aP in addition to x and y *)
  lazymatch goal with
    |- context [match ?v with pair x y => @?E x y end]
    => is_var v; idtac E
  end.

  (* maybe something like this, "using the variables bound in G"? *)
  lazymatch goal with
    |- context G [match ?v with pair x y => @?E x y G end]
    => is_var v; idtac E
  end.

Goal forall (P Q:nat*nat),
    { r | r =
    let (xP, yP) := P in
    let aP := xP + yP in
    let (xQ, yQ) := Q in
    let aQ := xQ + yQ in
    aP * aQ }.
Proof.
  eexists.
  etransitivity. Focus 2. {
    eapply Proper_prod_rect_changebody; [intro;intro|reflexivity].
(* Toplevel input, characters 0-114: *)
(* > lazymatch goal with       |- context G [match ?v with pair x y => @?E x y end]       => is_var v; idtac E     end. *)
(* > ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ *)
(* Error: No matching clauses for match. *)

*)