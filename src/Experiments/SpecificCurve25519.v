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
  Inductive nboundexpr : type -> Type :=
  | NConst : forall {t}, interp_type t -> nboundexpr t
  | NBinop : forall {t1 t2 t}, binop t1 t2 t -> var t1 -> var t2 -> nboundexpr t.
  Inductive nvar : type -> Type :=
  | NVar : forall {t}, var t -> nvar t
  | Nfst : forall {t1 t2}, nvar (Prod t1 t2) -> nvar t1
  | Nsnd : forall {t1 t2}, nvar (Prod t1 t2) -> nvar t2.
  Inductive npair : type -> Type :=
  | NVarInj : forall {t : simple_type}, nvar t -> npair t
  | NPair : forall {t1}, npair t1 -> forall {t2}, npair t2 -> npair (Prod t1 t2).
  Inductive nexpr : type -> Type :=
  | NLet : forall {tx}, nboundexpr tx -> forall {tC}, (var tx -> nexpr tC) -> nexpr tC
  | NPairInj : forall {tx}, npair tx -> nexpr tx.
End expr.
Local Notation ZConst z := (@Const _ TZ z%Z).
Arguments expr _ _ : clear implicits.
Arguments nexpr _ _ : clear implicits.
Arguments nvar _ _ : clear implicits.
Arguments npair _ _ : clear implicits.
Arguments nboundexpr _ _ : clear implicits.
Definition Expr t : Type := forall var, expr var t.

Definition partial_interp_once expr recr (t:type) :=
  match t with
  | Prod a b => prod (recr a) (recr b)
  | stype t' => expr t'
  end.
Fixpoint partial_interp_type expr (t:type) :=
  partial_interp_once expr (partial_interp_type expr) t.
Definition partial_interp_oncep (var:type -> Type) (t:type) := partial_interp_once var (npair var) t.

Fixpoint interp {t} (e:expr interp_type t) : interp_type t :=
  match e in expr _ t return interp_type t with
  | Const _ n => n
  | Var _ n => n
  | Binop _ _ _ op e1 e2 => interp_binop op (interp e1) (interp e2)
  | Let _ ex _ eC => let x := interp ex in interp (eC x)
  | Pair _ e1 _ e2 => (interp e1, interp e2)
  | MatchPair _ _ ep _ eC => let (v1, v2) := interp ep in interp (eC v1 v2)
  end.
Fixpoint nbinterp {t} (e:nboundexpr interp_type t) : interp_type t :=
  match e in nboundexpr _ t return interp_type t with
  | NConst _ v => v
  | NBinop _ _ _ op e1 e2 => interp_binop op e1 e2
  end.
Fixpoint nvinterp {t} (e:nvar interp_type t) : interp_type t :=
  match e in nvar _ t return interp_type t with
  | NVar _ v => v
  | Nfst _ _ p => fst (nvinterp p)
  | Nsnd _ _ p => snd (nvinterp p)
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

(*Fixpoint partial_npinterp {var} {t} (e:npair var t) : partial_interp_type var t.
  refine match e in npair _ t return partial_interp_type var t with
     | NVarInj _ v => _
     | _ => _ end; simpl in *.


Section under_lets.
  Context {var : type -> Type}.
  Fixpoint under_lets {te} (e:nexpr var te) {struct e} :
    forall {tC} (C:npair var te -> nexpr var tC), nexpr var tC :=
    match e in (nexpr _ t) return (forall tC : type, (npair var t -> nexpr var tC) -> nexpr var tC) with
    | @NLet _ tx ex teC eC => fun tC C => NLet ex (fun vx => @under_lets _ (eC vx) _ C)
    | @NPairInj _ _ e => fun _ C => C e
    end.

  Fixpoint under_pairs {te} (e:npair var te) {struct e} :
    forall {tC} (C:partial_interp_type var te -> nexpr var tC), nexpr var tC.
    refine match e in (npair _ t) return (forall tC : type, (partial_interp_type var t -> nexpr var tC) -> nexpr var tC) with
           | NPair _ a _ b
             =>
             _ | _ => _ end; simpl in *.
    | @NLet _ tx ex teC eC => fun tC C => NLet ex (fun vx => @under_lets_and_pairs _ (eC vx) _ C)
    | _ => _ end
    | @NPairInj _ _ e => fun _ C => C e
    end.

  (*Eval simpl in under_lets
                  (Let (ZConst 1) (fun v =>
                   Let (Binop OPZadd (Var v) (Var v)) (fun v' =>
                   Binop OPZsub (Var v') (Var v'))))

                  (fun e' => Binop OPZmul e' e')
                  .*)
End under_lets.



Fixpoint reify_struct {var} {t} : forall (v : interp_type t), nexpr var t
  := match t return forall (v : interp_type t), nexpr var t with
     | stype TZ => fun z => NLet (NConst z) (fun v => NPairInj (NVar v))
     | Prod A B
       => fun ab
          => under_lets
               (@reify_struct var _ (fst ab))
               (fun a
                => under_lets
                     (@reify_struct var _ (snd ab))
                     (fun b
                      => NPairInj (NPair a b)))
     end.

Fixpoint reify_struct_partial {var : type -> Type} {t} : forall (v : partial_interp_type var t), nexpr var t
  := match t return forall (v : partial_interp_type var t), nexpr var t with
     | stype _ => fun z => NPairInj (@NVar var _ z)
     | Prod A B
       => fun ab
          => under_lets
               (@reify_struct_partial var _ (fst ab))
               (fun a
                => under_lets
                     (@reify_struct_partial var _ (snd ab))
                     (fun b
                      => NPairInj (NPair a b)))
     end.

*)

Fixpoint partial_reflect {var} {t} : partial_interp_type (npair var) t -> npair var t
  := match t return partial_interp_type (npair var) t -> npair var t with
     | Prod a b => fun xy => NPair (partial_reflect (fst xy)) (partial_reflect (snd xy))
     | _ => fun xy => xy
     end.
(*Fixpoint smart_pair_Let {var} {tx} (ex : npair var tx) {tC} : forall (eC : partial_interp_oncep var tx -> nexpr var tC), nexpr var tC.
  refine match ex in npair _ tx return forall (eC : partial_interp_oncep var tx -> nexpr var tC), nexpr var tC with
         | NVar _ v => fun eC => eC v
         | NPair _ e1 _ e2 =>
           fun eC => _
         end.
simpl in *.
     | NLet _ ex' _ eC'
       => fun eC => NLet ex' (fun x' => @smart_Let _ _ (eC' x') _ eC)
     | _ => _ end.
Fixpoint smart_Let {var} {tx} (ex : nexpr var tx) {tC} : forall (eC : partial_interp_type var tx -> nexpr var tC), nexpr var tC.
  refine match ex in nexpr _ tx return forall (eC : partial_interp_type var tx -> nexpr var tC), nexpr var tC with
     | NLet _ ex' _ eC'
       => fun eC => NLet ex' (fun x' => @smart_Let _ _ (eC' x') _ eC)
     | _ => _ end.
     | NPairInj
       => *)
(*Fixpoint partial_reflect' {var} {t} : partial_interp_type var t -> nexpr var t.
  refine match t return partial_interp_type _ t -> nexpr _ t with
     | Prod a b => fun xy => NPair (@partial_reflect' _ _ (fst xy)) (@partial_reflect' _ _ (snd xy))
     | _ => _
     end.
Fixpoint partial_denote {var} {t} (x : npair (partial_interp_type var) t) : partial_interp_type var t
  := match x in npair _ t return partial_interp_type _ t with
     | NPair _ a _ b => (partial_denote a, partial_denote b)
     | NVar _ v => v
     end.*)



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
    | @Let _ tx ex tC eC =>
      under_lets
        (@subst_args _ ex)
        (fun ex => Let ex (fun vx => @flatten _ (eC vx)))
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
                   Let (Binop OPZadd (Var v) (Var v)) (fun v' =>
                   Binop OPZsub (Var v') (Var v'))))

                  (fun e' => Binop OPZmul e' e')
                  .
End under_lets.

Lemma under_lets_correct {te} (e:expr interp_type te) {tC} (C:expr interp_type te -> expr interp_type tC)
      (H:forall {t} (e:expr interp_type t) eC, interp (C (Let e eC)) = interp (C (eC (interp e)))) :
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
    Eval simpl in flatten (Let (Let (ZConst 1) (fun v => Let (Binop OPZadd (Var v) (Var v)) (fun v' => Pair (Var v') (Var v')))) (fun vp => MatchPair (Var vp) (fun a b => Var a ))).
End flatten.

Lemma flatten_correct {t} (e:expr interp_type t) :
      interp (flatten e) = interp e.
Proof. induction e; repeat (intuition congruence + simpl + rewrite under_lets_correct + rewrite_hyp !*). Qed.


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
    Time let e0 := (eval vm_compute in (Subst_args e)) in
    pose e0.
    rewrite <-unmatch_pair_correct.
    cbv iota beta delta [unmatch_pair CoqPairIfPair].
    rewrite <-flatten_correct.
    cbv iota beta delta [flatten under_lets].
    cbv iota beta delta [interp].
    reflexivity.
  Defined.
End Curve25519.



Section subst_args.
  Context {var : type -> Type}.
Set Printing Coercions.
  Fixpoint subst_args {t} (e:expr (partial_interp_type var) t) {struct e} : nexpr var t.
    refine match e in (expr _ t) return (nexpr var t) with
    | Const t n => reify_struct n
    | Var _ v => reify_struct_partial v
    | Let _ ex _ eC =>
      under_lets
        (@subst_args _ ex)
        (fun ex'
         => NLet ex' (fun v => @subst_args _ (eC (NVar v))))
    | _ => _ end; simpl in *.


    | _ => _
           end.
    | Binop t1 t2 t op e1 e2
      => under_lets
           (@subst_args _ e1)
           (smart_Let'
              (fun e1'
               => under_lets
                    (@subst_args _ e2)
                    (smart_Let'
                       (fun e2'
                        => Binop op (Var e1') (Var e2')))))
    | Pair _ e1 _ e2
      => under_lets (@subst_args _ e1)
                    (fun e1' => under_lets (@subst_args _ e2)
                                           (fun e2' => smart_Pair e1' e2'))
    | MatchPair _ _ ep _ eC =>
      under_lets (@subst_args _ ep)
                 (fun ep' => match is_arg ep', CoqPairIfPair ep' with
                             | true, Some (e1, e2) => @subst_args _ (eC e1 e2)
                             | _, _ => MatchPair ep' (fun x y => @subst_args _ (eC (Var x) (Var y)))
                             end)
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

Section flatten.
  Context {var : type -> Type}.
  Fixpoint flatten {t} (e:expr var t) {struct e} : expr var t :=
    match e in (expr _ t0) return (expr var t0) with
    | @Let _ tx ex tC eC =>
      under_lets (@flatten _ ex) (fun ex => Let ex (fun vx => @flatten _ (eC vx)))
    | e' => e'
    end.
    Eval simpl in flatten (Let (Let (ZConst 1) (fun v => Let (Binop OPZadd (Var v) (Var v)) (fun v' => Pair (Var v') (Var v')))) (fun vp => MatchPair (Var vp) (fun a b => Var a ))).
End flatten.

Lemma flatten_correct {t} (e:expr interp_type t) :
      interp (flatten e) = interp e.
Proof. induction e; repeat (intuition congruence + simpl + rewrite under_lets_correct + rewrite_hyp !*). Qed.


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
    clear e; pose e0.
    rewrite <-unmatch_pair_correct.
    cbv iota beta delta [unmatch_pair CoqPairIfPair].
    rewrite <-flatten_correct.
    cbv iota beta delta [flatten under_lets].
    cbv iota beta delta [interp].
    reflexivity.
  Defined.
End Curve25519.
