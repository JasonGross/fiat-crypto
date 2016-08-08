Require Import Crypto.Util.GlobalSettings.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Coq.ZArith.BinInt.


Inductive simple_type : Set := TZ.
Inductive type := stype (_ : simple_type) | Prod : type -> type -> type.
Coercion stype : simple_type >-> type.

Fixpoint interp_type (t:type) :=
  match t with
  | stype TZ => Z
  | Prod a b => prod (interp_type a) (interp_type b)
  end.

Ltac reify_type t :=
  lazymatch t with
  | BinInt.Z => uconstr:(stype TZ)
  | prod ?l ?r =>
    let l := reify_type l in
    let r := reify_type r in
    uconstr:(Prod l r)
  end.


Inductive binop : simple_type -> simple_type -> simple_type -> Set :=
| OPZadd : binop TZ TZ TZ
| OPZsub : binop TZ TZ TZ
| OPZmul : binop TZ TZ TZ
| OPZland : binop TZ TZ TZ
| OPZshiftr : binop TZ TZ TZ.
(* TODO: should [Pair] be a [binop]? *)

Definition interp_binop {t1 t2 t} (op:binop t1 t2 t) : interp_type t1 -> interp_type t2 -> interp_type t :=
  match op with
  | OPZadd    => Z.add
  | OPZsub    => Z.sub
  | OPZmul    => Z.mul
  | OPZland   => Z.land
  | OPZshiftr => Z.shiftr
  end.

Ltac reify_binop op :=
  lazymatch op with
  | Z.add    => OPZadd
  | Z.sub    => OPZsub
  | Z.mul    => OPZmul
  | Z.land   => OPZland
  | Z.shiftr => OPZshiftr
  end.



Section expr.
  Context {var : type -> Type}.
  Inductive expr : type -> Type :=
  | Const : forall {t}, interp_type t -> expr t
  | Var : forall {t}, var t -> expr t
  | Binop : forall {t1 t2 t}, binop t1 t2 t -> expr t1 -> expr t2 -> expr t
  | Let : forall {tx}, expr tx -> forall {tC}, (var tx -> expr tC) -> expr tC
  | Pair : forall {t1}, expr t1 -> forall {t2}, expr t2 -> expr (Prod t1 t2)
  | MatchPair : forall {t1 t2}, expr (Prod t1 t2) -> forall {tC}, (var t1 -> var t2 -> expr tC) -> expr tC.
End expr.
Arguments expr : clear implicits.

Section nexp.
  Context {var : type -> Type}.
  Inductive nvar : type -> Type :=
  | NVar : forall {t}, var t -> nvar t
  | Nfst : forall {t1 t2}, nvar (Prod t1 t2) -> nvar t1
  | Nsnd : forall {t1 t2}, nvar (Prod t1 t2) -> nvar t2.
  Inductive nboundexpr : type -> Type :=
  | NConst : forall {t}, interp_type t -> nboundexpr t
  | NBinop : forall {t1 t2 t}, binop t1 t2 t -> nvar t1 -> nvar t2 -> nboundexpr t.
  Inductive npair : type -> Type :=
  | NVarInj : forall {t : simple_type}, nvar t -> npair t
  | NPair : forall {t1}, npair t1 -> forall {t2}, npair t2 -> npair (Prod t1 t2).
  Inductive nexpr : type -> Type :=
  | NLet : forall {tx}, nboundexpr tx -> forall {tC}, (var tx -> nexpr tC) -> nexpr tC
  | NPairInj : forall {tx}, npair tx -> nexpr tx.

  Fixpoint refl (t : type) :=
    match t with
    | stype t' => nvar t'
    | Prod t0 t1 => prod (refl t0) (refl t1)
    end.

  Fixpoint reify_pair (t : type) : refl t -> npair t
    := match t return refl t -> npair t with
       | stype t' => fun e => NVarInj e
       | Prod t0 t1
         => fun e => NPair (@reify_pair t0 (fst e)) (@reify_pair t1 (snd e))
       end.

  Fixpoint reflect (t : type) (x : npair t) : refl t
    := match x in npair t return refl t with
       | NPair _ x0 _ x1 => (@reflect _ x0, @reflect _ x1)
       | NVarInj _ v => v
       end.

  Fixpoint reify_const t {tC} {struct t} : interp_type t -> (refl t -> nexpr tC) -> nexpr tC
    := match t return interp_type t -> (refl t -> nexpr tC) -> nexpr tC with
       | stype _
         => fun v F
            => NLet
                 (NConst v)
                 (fun v' => F (NVar v'))
       | Prod t0 t1
         => fun v F
            => @reify_const
                 t0 _ (fst v)
                 (fun v0
                  => @reify_const
                       t1 _ (snd v)
                       (fun v1
                        => F (v0, v1)))
       end.

  Fixpoint precompose_meaning t (e : expr refl t) {tC} {struct e} : (refl t -> nexpr tC) -> nexpr tC
    := match e in expr _ t return (refl t -> nexpr tC) -> nexpr tC with
       | Const _ x => @reify_const _ _ x
       | Var _ x => fun f => f x
       | Binop _ _ _ f e0 e1
         => fun F
            => @precompose_meaning
                 _ e0 _
                 (fun e0'
                  => @precompose_meaning
                       _ e1 _
                       (fun e1'
                        => NLet (NBinop f e0' e1') (fun x => F (NVar x))))
       | Let _ x _ e
         => fun F
            => @precompose_meaning
                 _ x _
                 (fun x'
                  => @precompose_meaning
                       _ (e x') _
                       (fun ex'
                        => F ex'))
       | Pair _ e0 _ e1
         => fun F
            => @precompose_meaning
                 _ e0 _
                 (fun e0'
                  => @precompose_meaning
                       _ e1 _
                       (fun e1'
                        => F (e0', e1')))
       | MatchPair _ _ x _ b
         => fun F
            => @precompose_meaning
                 _ x _
                 (fun x'
                  => @precompose_meaning
                       _ (b (fst x') (snd x')) _
                       (fun bx
                        => F bx))
       end.

  Definition normalize t (e : expr refl t) : nexpr t := precompose_meaning _ e (fun x => NPairInj (reify_pair _ x)).

End nexp.


Local Notation ZConst z := (@Const _ TZ z%Z).
Arguments expr _ _ : clear implicits.
Arguments nexpr _ _ : clear implicits.
Arguments nvar _ _ : clear implicits.
Arguments npair _ _ : clear implicits.
Arguments nboundexpr _ _ : clear implicits.
Definition Expr t : Type := forall var, expr var t.
Definition NExpr t : Type := forall var, nexpr var t.

Fixpoint interp {t} (e:expr interp_type t) : interp_type t :=
  match e in expr _ t return interp_type t with
  | Const _ n => n
  | Var _ n => n
  | Binop _ _ _ op e1 e2 => interp_binop op (interp e1) (interp e2)
  | Let _ ex _ eC => let x := interp ex in interp (eC x)
  | Pair _ e1 _ e2 => (interp e1, interp e2)
  | MatchPair _ _ ep _ eC => let (v1, v2) := interp ep in interp (eC v1 v2)
  end.
Fixpoint nvinterp {t} (e:nvar interp_type t) : interp_type t :=
  match e in nvar _ t return interp_type t with
  | NVar _ v => v
  | Nfst _ _ p => fst (nvinterp p)
  | Nsnd _ _ p => snd (nvinterp p)
  end.
Fixpoint nbinterp {t} (e:nboundexpr interp_type t) : interp_type t :=
  match e in nboundexpr _ t return interp_type t with
  | NConst _ v => v
  | NBinop _ _ _ op e1 e2 => interp_binop op (nvinterp e1) (nvinterp e2)
  end.
Fixpoint npinterp {t} (e:npair interp_type t) : interp_type t :=
  match e in npair _ t return interp_type t with
  | NVarInj _ v => nvinterp v
  | NPair _ e1 _ e2 => (npinterp e1, npinterp e2)
  end.

Fixpoint ninterp {t} (e:nexpr interp_type t) : interp_type t :=
  match e in nexpr _ t return interp_type t with
  | NLet _ ex _ eC => let x := nbinterp ex in ninterp (eC x)
  | NPairInj _ p => npinterp p
  end.
Definition Interp {t} (E:Expr t) : interp_type t := interp (E interp_type).


Example example_expr : interp (Let (ZConst 7) (fun a => Let (Let (Binop OPZadd (Var a) (Var a)) (fun b => Pair (Var b) (Var b))) (fun p => MatchPair (Var p) (fun x y => Binop OPZadd (Var x) (Var y))) )) = 28%Z. reflexivity. Qed.

Class reify {varT} (var:varT) {eT} (e:eT) {T:Type} := Build_reify : T.
Definition reify_var_for_in_is {T} (x:T) (t:type) {eT} (e:eT) := False.
Class is_var {T} (x : T) := mk_is_var : True.
Hint Extern 0 (is_var ?t) => is_var t; exact I : typeclass_instances.
Ltac reify var e :=
  lazymatch e with
  | let x := ?ex in @?eC x =>
    let ex := reify var ex in
    let eC := reify var eC in
    uconstr:(Let(var:=var) ex eC)
  | match ?ep with (v1, v2) => @?eC v1 v2 end =>
    let ep := reify var ep in
    let eC := reify var eC in
    uconstr:(MatchPair(var:=var) ep eC)
  | pair ?a ?b =>
    let a := reify var a in
    let b := reify var b in
    uconstr:(Pair(var:=var) a b)
  | ?op ?a ?b =>
      let op := reify_binop op in
      let b := reify var b in
      let a := reify var a in
      uconstr:(Binop(var:=var) op a b)
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
    | _:reify_var_for_in_is x ?t ?v |- _ => uconstr:(@Var var t v)
    | _ => let t := match type of x with ?t => reify_type t end in
           uconstr:(@Const var t x)
    end
  end.
Hint Extern 0 (reify ?var ?e) => (let e := reify var e in exact e) : typeclass_instances.

Ltac Reify e :=
  lazymatch constr:(fun (var:type->Type) => (_:reify var e)) with
    (fun var => ?C) => constr:(fun (var:type->Type) => C) (* copy the term but not the type cast *)
  end.

Goal forall (x : Z) (v : interp_type TZ) (_:reify_var_for_in_is x TZ v), reify(T:=Z) interp_type ((fun x => x+x) x)%Z.
  intros.
  let A := reify interp_type (x + x)%Z in
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
  let e := fresh "e" in
  pose rhs as e (*
  let lhs := lhs_of_goal in
  change (lhs = interp (rhs interp_type))*).

Goal (0 = let x := 1+2 in x*3)%Z.
  Reify_rhs.
Abort.

Goal (0 = let x := 1 in let y := 2 in x * y)%Z.
  Reify_rhs.
Abort.

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

Lemma unmatch_pair_correct : forall {t} (e:expr interp_type t), interp (unmatch_pair e) = interp e.
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

(*Goal forall x y:Z, ((let x0 := x in let x1 := y in (x0 * x1))
                    = match (x, y) with (a, b) => a*b end)%Z.
  intros.
  Reify_rhs.
  rewrite <-unmatch_pair_correct.
  cbv iota beta delta [unmatch_pair CoqPairIfPair].
  cbv iota beta delta [interp].
  reflexivity.
Qed.*)

(*Lemma under_lets_correct {te} (e:expr interp_type te) {tC} (C:expr interp_type te -> expr interp_type tC)
      (H:forall {t} (e:expr interp_type t) eC, interp (C (Let e eC)) = interp (C (eC (interp e)))) :
  interp (under_lets e C) = interp (C e).
Proof. induction e; repeat (intuition congruence + simpl + rewrite_hyp !* ). Qed.*)

(*Fixpoint is_arg {var t} (e:expr var t) : bool :=
  match e with
  | Var _ _ => true
  | Pair _ e1 _ e2 => is_arg e1 && is_arg e2
  | _ => false
  end.

Definition smart_Let {var} {tx} (ex : expr var tx) : forall {tC} (eC : var tx -> expr var tC), expr var tC
  := match ex in expr _ tx return forall {tC} (eC : var tx -> expr var tC), expr var tC with
     | Var _ v => fun _ eC => eC v
     | ex' => fun _ eC => Let ex' eC
     end.
Definition smart_Let' {var} {tx} {tC} (eC : var tx -> expr var tC) (ex : expr var tx) : expr var tC
  := smart_Let ex eC.
Definition smart_Pair {var} {t1 t2} (e1 : expr var t1) (e2 : expr var t2) : expr var (Prod t1 t2)
  := match e1 in expr _ t1, e2 in expr _ t2 return expr _ (Prod t1 t2) with
     | Var _ _ as e1', Var _ _ as e2'
     | Var _ _ as e1', @Pair _ _ _ _ _ as e2'
     | @Pair _ _ _ _ _ as e1', Var _ _ as e2'
     | @Pair _ _ _ _ _ as e1', @Pair _ _ _ _ _ as e2'
       => Pair e1' e2'
     | e1', e2'
       => Let e1' (fun e1'' => Let e2' (fun e2'' => Pair (Var e1'') (Var e2'')))
     end.
*)
Section subst_args.
  Context {var : type -> Type}.

  Definition subst_args {t} (e:expr _ t) : nexpr var t
    := normalize t e.
End subst_args.
Definition Subst_args {t} (e:Expr t) : NExpr t := fun var => subst_args (e _).


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

Lemma reassoc_let_correct : forall {t} (e:expr interp_type t), interp (reassoc_let e) = interp e.
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

    Time Reify_rhs. (* Coq trunk July 2016: 48s *)
    Set Printing Depth 99999.
    exfalso.
    Time vm_compute in e.
    Time let e0 := (eval vm_compute in (Subst_args e)) in
    clear e; pose e0 as e.
    rewrite <-unmatch_pair_correct.
    cbv iota beta delta [unmatch_pair CoqPairIfPair].
    rewrite <-flatten_correct.
    cbv iota beta delta [flatten under_lets].
    cbv iota beta delta [interp].
    reflexivity.
  Defined.
End Curve25519.
