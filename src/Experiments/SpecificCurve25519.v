Require Import Crypto.Util.GlobalSettings.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Coq.ZArith.BinInt.

Inductive type := TZ | Prod : type -> type -> type.

Fixpoint tinterp (t:type) :=
  match t with
  | TZ => Z
  | Prod a b => prod (tinterp a) (tinterp b)
  end.

Section expr.
  Context {var : type -> Type}.
  Inductive expr : type -> Type :=
  | Const : forall {t}, tinterp t -> expr t
  | Var : forall {t}, var t -> expr t
  | Binop : forall {t1 t2 t}, (tinterp t1->tinterp t2->tinterp t) -> expr t1 -> expr t2 -> expr t
  | Let : forall {tx}, expr tx -> forall {tC}, (var tx -> expr tC) -> expr tC
  | Pair : forall {t1}, expr t1 -> forall {t2}, expr t2 -> expr (Prod t1 t2)
  | MatchPair : forall {t1 t2}, expr (Prod t1 t2) -> forall {tC}, (var t1 -> var t2 -> expr tC) -> expr tC.
End expr.
Arguments expr _ _ : clear implicits.
Definition Expr t : Type := forall var, expr var t.

Local Notation ZConst z := (@Const _ TZ z%Z).
Local Notation ZBinop op a b := (@Binop _ TZ TZ TZ op%Z a%Z b%Z).

Fixpoint interp {t} (e:expr tinterp t) : tinterp t :=
  match e in expr _ t return tinterp t with
  | Const _ n => n
  | Var _ n => n
  | Binop _ _ _ op e1 e2 => op (interp e1) (interp e2)
  | Let _ ex _ eC => let x := interp ex in interp (eC x)
  | Pair _ e1 _ e2 => (interp e1, interp e2)
  | MatchPair _ _ ep _ eC => let (v1, v2) := interp ep in interp (eC v1 v2)
  end.
Definition Interp {t} (E:Expr t) : tinterp t := interp (E tinterp).

Example example_expr : interp (Let (ZConst 7) (fun a => Let (Let (@Binop _ TZ TZ TZ Z.add (Var a) (Var a)) (fun b => Pair (Var b) (Var b))) (fun p => MatchPair (Var p) (fun x y => @Binop _ TZ TZ TZ Z.add (Var x) (Var y))) )) = 28%Z. reflexivity. Qed.

Section unmatch_pair.
  Context {var : type -> Type}.
  Definition CoqPairIfPair {t1 t2} (ep : expr var (Prod t1 t2)) : option (expr var t1 * expr var t2)
   := match ep in expr _ t return option (match t with
                                          | Prod t1 t2 => (expr var t1 * expr var t2)
                                          | _ => False
                                          end) with
      | Pair _ e1 _ e2 => Some (e1, e2)
      | _ => None
      end.

  Fixpoint unmatch_pair {t} (e:expr var t) : expr var t :=
    match e in expr _ t return expr var t with
    | MatchPair _ _ ep _ eC
      => match CoqPairIfPair (unmatch_pair ep) with
         | Some (e1, e2) => Let e1 (fun v1 => (Let e2 (fun v2 => unmatch_pair (eC v1 v2))))
         | None => MatchPair (unmatch_pair ep) (fun x y => unmatch_pair (eC x y))
         end
    | Const _ n => Const n
    | Var _ n => Var n
    | Binop _ _ _ op e1 e2 => Binop op (unmatch_pair e1) (unmatch_pair e2)
    | Let _ ex _ eC => Let (unmatch_pair ex) (fun x => unmatch_pair (eC x))
    | Pair _ e1 _ e2 => Pair (unmatch_pair e1) (unmatch_pair e2)
    end.
End unmatch_pair.

Ltac simpl_lem_then_rewrite lem :=
  let t := type of lem in
  let t' := (eval simpl in t) in
  let lem' :=  constr:(lem:t') in
  rewrite lem'.

Lemma CoqPairIfPair_Some_helper {var} {t} (ep:expr var t) :
  match t return expr var t -> Prop with
  | Prod _ _ => fun ep => forall e1 e2, CoqPairIfPair ep = Some (e1, e2) <-> ep = Pair e1 e2
  | _ => fun _ => True
  end ep.
Proof.
  unfold CoqPairIfPair; destruct ep; try break_match;
    repeat (intuition congruence || match goal with [H:_ |- _] => apply (f_equal CoqPairIfPair) in H end).
Qed.

Lemma CoqPairIfPair_Some {var} {t1 t2} (ep:expr var (Prod t1 t2)) e1 e2 :
    CoqPairIfPair ep = Some (e1, e2) <-> ep = Pair e1 e2.
Proof.
  simpl_lem_then_rewrite (CoqPairIfPair_Some_helper ep); reflexivity.
Qed.

Lemma unmatch_pair_correct : forall {t} (e:expr tinterp t), interp (unmatch_pair e) = interp e.
  induction e; simpl;
    try destruct (interp e) eqn:Heqe;
    repeat break_match; simpl;
    try find_apply_lem_hyp @CoqPairIfPair_Some;
    repeat match goal with
           | _ => solve [intuition]
           | _ => progress simpl @interp in *
           | [H: _ |- _ ] => rewrite H
           | [H: _, H': _ |- _ ] => rewrite H in H'
           | [H: (_, _) = (_, _) |- _ ] => inversion H; subst
           end.
Qed.

Section subst_args.
  Context {var : type -> Type}.
  Fixpoint is_arg {t} (e:expr (expr var) t) : bool :=
    match e with
    | Var _ _ => true
    | Pair _ e1 _ e2 => is_arg e1 && is_arg e2
    | _ => false
    end.
  Fixpoint subst_args {t} (e:expr (expr var) t) {struct e} : expr var t :=
    match e in (expr _ t) return (expr var t) with
    | Const _ n => Const n
    | Var _ v => v
    | Binop _ _ _ op e1 e2 => Binop op (@subst_args _ e1) (@subst_args _ e2)
    | Let _ ex _ eC =>
      if is_arg ex
      then @subst_args _ (eC (@subst_args _ ex))
      else Let (@subst_args _ ex) (fun v => @subst_args _ (eC (Var v)))
    | Pair _ e1 _ e2 => Pair (@subst_args _ e1) (@subst_args _ e2)
    | MatchPair _ _ ep _ eC =>
      match is_arg ep, CoqPairIfPair (@subst_args _ ep) with
      | true, Some (e1, e2) => @subst_args _ (eC e1 e2)
      | _, _ => MatchPair (@subst_args _ ep) (fun x y => @subst_args _ (eC (Var x) (Var y)))
      end
    end.
End subst_args.
Definition Subst_args {t} (e:Expr t) : Expr t := fun var => subst_args (e (expr var)).


Section reassoc_let.
  Context {var : type -> Type}.

  Definition matchLetLetInIn {t} (e:expr var t) :
    option (sigT (fun tx:type => (expr var tx * (var tx -> expr var t))%type)) :=
    match e with Let _ ex _ eC => Some (existT _ _ (ex, eC)) | _ => None end.

  Fixpoint reassoc_let {t} (e:expr var t) {struct e} : expr var t :=
    match e in expr _ t return expr var t with
    | Let _ ex _ eC =>
      match matchLetLetInIn ex with
      | Some (existT tx' (ex', eC')) =>
        Let ex' (fun v' => Let (eC' v') (fun v => reassoc_let (eC v)))
      | None => Let (reassoc_let ex) (fun v => reassoc_let (eC v))
      end
    | Const _ n => Const n
    | Var _ n => Var n
    | Binop _ _ _ op e1 e2 => Binop op (reassoc_let e1) (reassoc_let e2)
    | Pair _ e1 _ e2 => Pair (reassoc_let e1) (reassoc_let e2)
    | MatchPair _ _ ep _ eC => MatchPair (reassoc_let ep) (fun x y => reassoc_let (eC x y))
    end.
End reassoc_let.

Lemma matchLetLetInIn_Some {var} {t} (e:expr var t) {tx} ex eC :
  matchLetLetInIn e = Some (existT _ tx (ex, eC)) <-> e = Let ex eC.
Proof.
Admitted.

Lemma reassoc_let_correct : forall {t} (e:expr tinterp t), interp (reassoc_let e) = interp e.
  induction e;
    repeat match goal with
           | [H: _ |- _ ] => simpl_lem_then_rewrite H
           | [H: _ |- _ ] => rewrite matchLetLetInIn_Some in H
           | _ => break_match
           | _ => progress simpl
           | _ => progress subst
           | _ => solve [intuition congruence]
           end.
Qed.

Section under_lets.
  Context {var : type -> Type}.
  Fixpoint under_lets {te} (e:expr var te) {struct e} :
    forall {tC} (C:expr var te -> expr var tC), expr var tC :=
    match e in (expr _ t) return (forall tC : type, (expr var t -> expr var tC) -> expr var tC) with
    | @Let _ tx ex teC eC => fun tC C => Let ex (fun vx => @under_lets _ (eC vx) _ C)
    | e' => fun _ C => C e'
    end.
    
  Eval simpl in under_lets
                  (Let (ZConst 1) (fun v =>
                   Let (ZBinop Z.add (Var v) (Var v)) (fun v' =>
                   ZBinop (fun a b => a) (Var v') (Var v'))))

                  (fun e' => ZBinop Z.div e' e')
                  .
End under_lets.

Lemma under_lets_correct {te} (e:expr tinterp te) {tC} (C:expr tinterp te -> expr tinterp tC)
      (H:forall {t} (e:expr tinterp t) eC, interp (C (Let e eC)) = interp (C (eC (interp e)))) :
  interp (under_lets e C) = interp (C e).
Proof. induction e; repeat (intuition congruence + simpl + rewrite_hyp !*). Qed.

Section flatten.
  Context {var : type -> Type}.
  Fixpoint flatten {t} (e:expr var t) {struct e} : expr var t :=
    match e in (expr _ t0) return (expr var t0) with
    | @Let _ tx ex tC eC =>
      under_lets (@flatten _ ex) (fun ex => Let ex (fun vx => @flatten _ (eC vx)))
    | e' => e'
    end.
    Eval simpl in flatten (Let (Let (ZConst 1) (fun v => Let (@Binop _ TZ TZ TZ Z.add (Var v) (Var v)) (fun v' => Pair (Var v') (Var v')))) (fun vp => MatchPair (Var vp) (fun a b => Var a ))).
End flatten.

Lemma flatten_correct {t} (e:expr tinterp t) :
      interp (flatten e) = interp e.
Proof. induction e; repeat (intuition congruence + simpl + rewrite under_lets_correct + rewrite_hyp !*). Qed.

(* The [reify] tactic below avoids beta-exapnsion while recursing under binders. *)
(* To do this, it has to manipulate open terms. *)
(* An alternative would be to allow beta-expansion and then perform one beta reduction at the head of the term *)
(* One black magic hack for doing that in 8.4 relies on immediate reduction of trivial matches: *)
(*
Ltac beta_head term := (*do just first beta reduction*)
lazymatch term with
| ((fun a => ?t) ?v) => constr:(match v with a => t end)
end.
*)
(* More sane (but not 8.4-compatible code) here:
Ltac zeta_head term :=
  lazymatch term with
    (let a := ?v in ?B) =>
    let r := fresh in
    lazymatch
        constr:(let a := v in
                let r := B in
                ltac:(subst a; let z := get_value r in exact z)) with
      (let _ := _ in let _ := _ in ?B') => B'
    end
  end.
Ltac beta_head term :=
  lazymatch term with
    ((fun a => ?v) ?b) =>
    let term' := constr:(let a := b in v) in
    zeta_head term'
  end.
*)

Ltac reify_type t :=
  lazymatch t with
  | BinInt.Z => constr:(TZ)
  | prod ?l ?r =>
    let l := reify_type l in
    let r := reify_type r in
    constr:(Prod l r)
  end.

Class reify {varT} (var:varT) {eT} (e:eT) {T:Type} := Build_reify : T.
Definition reify_var_for_in_is {T} (x:T) (t:type) {eT} (e:eT) := False.

Ltac type_of x := match type of x with ?t => constr:(t) end.
Ltac reify_type_of x :=
  let t := type_of x in
  reify_type t.

Ltac reify var e :=
  lazymatch e with
  | let x := ?ex in @?eC x =>
    let ex := reify var ex in
    let eC := reify var eC in
    constr:(Let(var:=var) ex eC)
  | match ?ep with (v1, v2) => @?eC v1 v2 end =>
    let ep := reify var ep in
    let eC := reify var eC in
    constr:(MatchPair(var:=var) ep eC)
  | pair ?a ?b =>
    let a := reify var a in
    let b := reify var b in
    constr:(Pair(var:=var) a b)
  | ?op ?a ?b =>
    lazymatch type of op with
      ?t1->?t2->?t =>
      let t1 := reify_type t1 in
      let t2 := reify_type t2 in
      let t := reify_type t in
      let b := reify var b in
      let a := reify var a in
      constr:(@Binop var t1 t2 t op a b)
    end
  | (fun x : ?T => ?C) =>
    let t := reify_type T in
    (* Work around Coq 8.5 and 8.6 bug *)
    (* <https://coq.inria.fr/bugs/show_bug.cgi?id=4998> *)
    (* Avoid re-binding the Gallina variable referenced by Ltac [x] *)
    (* even if its Gallina name matches a Ltac in this tactic. *)
    let maybe_x := fresh x in
    let not_x := fresh x in
    lazymatch constr:(fun (x : T) (not_x : var t) (_:reify_var_for_in_is x t not_x) =>
                        (_ : reify var C)) (* [C] here is an open term that references "x" by name *)
    with fun _ v _ => @?C v => C end
  | ?x =>
    lazymatch goal with
    | _:reify_var_for_in_is x ?t ?v |- _ => constr:(@Var var t v)
    | _ => let t := reify_type_of x in  constr:(@Const var t x)
    end
  end.
Hint Extern 0 (reify ?var ?e) => (let e := reify var e in eexact e) : typeclass_instances.

Ltac Reify e :=
  lazymatch constr:(fun (var:type->Type) => (_:reify var e)) with
    (fun var => ?C) => constr:(fun (var:type->Type) => C) (* copy the term but not the type cast *)
  end.

Goal forall (x : Z) (v : tinterp TZ) (_:reify_var_for_in_is x TZ v), reify(T:=Z) tinterp ((fun x => x+x) x)%Z.
  intros.
  let A := reify tinterp (x + x)%Z in
  pose A.
Abort.

Goal False.
  let z := Reify (let x := 0 in x)%Z in pose z.
Abort.
  
Ltac lhs_of_goal := match goal with |- ?R ?LHS ?RHS => constr:(LHS) end.
Ltac rhs_of_goal := match goal with |- ?R ?LHS ?RHS => constr:(RHS) end.
Ltac Reify_rhs :=
  let rhs := rhs_of_goal in
  let rhs := Reify rhs in
  let lhs := lhs_of_goal in
  change (lhs = interp (rhs tinterp)).

Goal (0 = let x := 1+2 in x*3)%Z.
  Reify_rhs.
Abort.

Goal (0 = let x := 1 in let y := 2 in x * y)%Z.
  Reify_rhs.
Abort.

Goal forall x y:Z, ((let x0 := x in let x1 := y in (x0 * x1))
                    = match (x, y) with (a, b) => a*b end)%Z.
  intros.
  Reify_rhs.
  rewrite <-unmatch_pair_correct.
  cbv iota beta delta [unmatch_pair CoqPairIfPair].
  cbv iota beta delta [interp].
  reflexivity.
Qed.



Require Import Crypto.Util.Notations .
Require Import Crypto.Specific.GF25519.
Require Import Crypto.CompleteEdwardsCurve.ExtendedCoordinates.

Local Infix "<<" := Z.shiftr.
Local Infix "&" := Z.land.
Section Curve25519.
  Definition ge25519_add' (twice_d : fe25519) :=
    Eval cbv beta delta [Extended.add_coordinates fe25519 add mul sub ModularBaseSystemOpt.Let_In] in
      @Extended.add_coordinates fe25519 add sub mul twice_d.

  Definition ge25519_add_sig (twice_d : fe25519) : forall P1 P2, { r | r = ge25519_add' twice_d P1 P2 }.
    intros.

    hnf in twice_d.
    repeat match goal with p:prod _ _ |- _ => destruct p end.
    eexists.
    cbv beta delta [ge25519_add'].
    
    Reify_rhs. (* Coq trunk July 2016: 47s *)
    Set Printing Depth 99999.
    rewrite <-unmatch_pair_correct.
    cbv iota beta delta [unmatch_pair CoqPairIfPair].
    rewrite <-flatten_correct.
    cbv iota beta delta [flatten under_lets].
    cbv iota beta delta [interp].
    reflexivity.
  Defined.
End Curve25519.