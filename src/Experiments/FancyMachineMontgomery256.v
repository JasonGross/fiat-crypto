Require Import Coq.ZArith.ZArith.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.ArchitectureToZLike.
Require Import Crypto.BoundedArithmetic.ArchitectureToZLikeProofs.
Require Import Crypto.ModularArithmetic.Montgomery.ZBounded.
Require Import Crypto.Util.Tuple.


Require Import Bedrock.Word.
Require Import Crypto.Util.GlobalSettings.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.

Require Import Crypto.Assembly.Evaluables.

Local Open Scope Z_scope.
Notation eta x := (fst x, snd x).
Notation eta3 x := (eta (fst x), snd x).

Section fold.
  Context {A B} (f : A -> B) (join : B -> B -> B).
  Fixpoint tuple'_fold {n : nat} : tuple' A n -> B
    := match n with
       | 0%nat => fun v => f v
       | S n' => fun v => join (tuple'_fold (fst v)) (f (snd v))
       end.

  Definition tuple_fold (init : B) {n : nat} : tuple A n -> B
    := match n with
       | 0%nat => fun v => init
       | S n' => tuple'_fold
       end.
End fold.

Axiom (modulus : Z) (m' : Z) (Hm : modulus <> 0) (H : 0 <= modulus < 2^256) (Hm' : 0 <= m' < 2^256) (ops : fancy_machine.instructions (2 * 128)) (props : fancy_machine.arithmetic ops).
Let H' : 0 <= 256 <= 256. omega. Qed.
Let H'' : 0 < 256. omega. Qed.
Let props' := ZLikeProperties_of_ArchitectureBoundedOps ops modulus H 256 H' H''.
Let ops' := (ZLikeOps_of_ArchitectureBoundedOps ops modulus 256).
Let fst' := @fst fancy_machine.W fancy_machine.W.
Let snd' := @snd fancy_machine.W fancy_machine.W.
Let ldi : load_immediate
            (@ZBounded.SmallT (2 ^ 256) (2 ^ 256) modulus
                              (@ZLikeOps_of_ArchitectureBoundedOps 128 ops modulus 256)) := _.
Let isldi : is_load_immediate ldi := _.
Let f := (fun v => proj1_sig (partial_reduce (2^256) modulus (props := props') (ldi m') I Hm (fst' v, snd' v))).

Section Definitions.
  Inductive vartype := Tbool | TW.
  Inductive consttype := TZ.
  Inductive type := Tvar (_ : vartype) | Tconst (_ : consttype) | Prod : type -> type -> type.
  Global Coercion Tvar : vartype >-> type.
  Global Coercion Tconst : consttype >-> type.

  Fixpoint interp_type (t:type): Type :=
    match t with
    | Prod a b => prod (interp_type a) (interp_type b)
    | TZ => Z
    | TW => fancy_machine.W
    | Tbool => bool
    end.

  Section ind.
    Local Notation TZ := (Tconst TZ).
    Local Notation TW := (Tvar TW).
    Local Notation Tbool := (Tvar Tbool).
    Inductive nop : forall (narg nret : nat), tuple type narg -> tuple type nret -> Type :=
    | OPldi     : nop 1 1 TZ TW
    | OPshrd    : nop 3 1 (TW, TW, TZ) TW
    | OPshl     : nop 2 1 (TW, TZ) TW
    | OPshr     : nop 2 1 (TW, TZ) TW
    | OPmkl     : nop 2 1 (TW, TZ) TW
    | OPadc     : nop 3 2 (TW, TW, Tbool) (Tbool, TW)
    | OPsubc    : nop 3 2 (TW, TW, Tbool) (Tbool, TW)
    | OPmulhwll : nop 2 1 (TW, TW) TW
    | OPmulhwhl : nop 2 1 (TW, TW) TW
    | OPmulhwhh : nop 2 1 (TW, TW) TW
    | OPselc    : nop 3 1 (Tbool, TW, TW) TW
    | OPaddm    : nop 3 1 (TW, TW, TW) TW.
  End ind.

  Definition interp_nop {narg nret t1 t2} (op:@nop narg nret t1 t2)
    : tuple_fold interp_type prod unit t1
      -> tuple_fold interp_type prod unit t2
    := match op in (@nop narg nret t1 t2)
             return tuple_fold interp_type prod unit t1
                    -> tuple_fold interp_type prod unit t2
       with
       | OPldi => fun args => ldi args
       | OPshrd => fun args => let '(x1, x2, x3) := eta3 args in shrd x1 x2 x3
       | OPshl => fun args => let '(x1, x2) := eta args in shl x1 x2
       | OPshr => fun args => let '(x1, x2) := eta args in shr x1 x2
       | OPmkl => fun args => let '(x1, x2) := eta args in mkl x1 x2
       | OPadc => fun args => let '(x1, x2, x3) := eta3 args in adc x1 x2 x3
       | OPsubc => fun args => let '(x1, x2, x3) := eta3 args in subc x1 x2 x3
       | OPmulhwll => fun args => let '(x1, x2) := eta args in mulhwll x1 x2
       | OPmulhwhl => fun args => let '(x1, x2) := eta args in mulhwhl x1 x2
       | OPmulhwhh => fun args => let '(x1, x2) := eta args in mulhwhh x1 x2
       | OPselc => fun args => let '(x1, x2, x3) := eta3 args in selc x1 x2 x3
       | OPaddm => fun args => let '(x1, x2, x3) := eta3 args in addm x1 x2 x3
       end.
End Definitions.

Module Input.
  Section Language.
    Section expr.
      Context {var : type -> Type}.

      Inductive expr : type -> Type :=
      | Const : forall {t}, interp_type t -> expr t
      | Var : forall {t}, var t -> expr t
      | Unop : forall {t1 t2}, @nop 1 1 t1 t2
                               -> expr t1 -> expr (tuple_fold id Prod TZ t2)
      | Binop : forall {t10 t11 t2}, @nop 2 1 (t10, t11) t2
                                     -> expr t10 -> expr t11 -> expr (tuple_fold id Prod TZ t2)
      | Trinop : forall {t10 t11 t12 t2}, @nop 3 1 (t10, t11, t12) t2
                                          -> expr t10 -> expr t11 -> expr t12 -> expr (tuple_fold id Prod TZ t2)
      | Trinop2Ret : forall {t10 t11 t12 t2}, @nop 3 2 (t10, t11, t12) t2
                                              -> expr t10 -> expr t11 -> expr t12 -> expr (tuple_fold id Prod TZ t2)
      | Let : forall {tx}, expr tx -> forall {tC}, (var tx -> expr tC) -> expr tC
      | Pair : forall {t1}, expr t1 -> forall {t2}, expr t2 -> expr (Prod t1 t2)
      | MatchPair : forall {t1 t2}, expr (Prod t1 t2) -> forall {tC}, (var t1 -> var t2 -> expr tC) -> expr tC.
    End expr.

    Local Notation ZConst z := (@Const Z ZEvaluable _ z%Z).

    Definition Expr t : Type := forall var, @expr var t.

    Fixpoint interp {t} (e: @expr interp_type t) : interp_type t :=
      match e in @expr _ t return interp_type t with
      | Const _ n => n
      | Var _ n => n
      | Unop _ _ op e1 => interp_nop op (interp e1)
      | Binop _ _ _ op e1 e2 => interp_nop op (interp e1, interp e2)
      | Trinop _ _ _ _ op e1 e2 e3 => interp_nop op (interp e1, interp e2, interp e3)
      | Trinop2Ret _ _ _ _ op e1 e2 e3 => interp_nop op (interp e1, interp e2, interp e3)
      | Let _ ex _ eC => let x := interp ex in interp (eC x)
      | Pair _ e1 _ e2 => (interp e1, interp e2)
      | MatchPair _ _ ep _ eC => let (v1, v2) := interp ep in interp (eC v1 v2)
      end.

    Definition Interp {t} (E:Expr t) : interp_type t := interp (E interp_type).
  End Language.

  (* Reification assumes the argument type is Z *)

  Ltac reify_type t :=
    lazymatch t with
    | BinInt.Z => TZ
    | bool => Tbool
    | fancy_machine.W => TW
    | prod ?l ?r =>
      let l := reify_type l in
      let r := reify_type r in
      constr:(Prod l r)
    end.

  Ltac reify_nop op :=
    lazymatch op with
    | @Interface.ldi     => OPldi
    | @Interface.shrd    => OPshrd
    | @Interface.shl     => OPshl
    | @Interface.shr     => OPshr
    | @Interface.mkl     => OPmkl
    | @Interface.adc     => OPadc
    | @Interface.subc    => OPsubc
    | @Interface.mulhwll => OPmulhwll
    | @Interface.mulhwhl => OPmulhwhl
    | @Interface.mulhwhh => OPmulhwhh
    | @Interface.selc    => OPselc
    | @Interface.addm    => OPaddm
    end.

  Class reify {varT} (var:varT) {eT} (e:eT) {T:Type} := Build_reify : T.
  Definition reify_var_for_in_is {T} (x:T) (t:type) {eT} (e:eT) := False.

  Ltac reify var e :=
    lazymatch e with
    | let x := ?ex in @?eC x =>
      let ex := reify var ex in
      let eC := reify var eC in
      constr:(Let (var:=var) ex eC)
    | match ?ep with (v1, v2) => @?eC v1 v2 end =>
      let ep := reify var ep in
      let eC := reify var eC in
      constr:(MatchPair (var:=var) ep eC)
    | pair ?a ?b =>
      let a := reify var a in
      let b := reify var b in
      constr:(Pair (var:=var) a b)
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
    | ?x
      => lazymatch goal with
         | _:reify_var_for_in_is x ?t ?v |- _ => constr:(@Var var t v)
         | _
           => let op := head x in
              let op := match x with
                        | _ => reify_nop op
                        | _ => let t := (let t := type of x in reify_type t) in
                               constr:(@Const var t x)
                        end in
              lazymatch op with
              | @Const _ _ _ => op
              | _
                => let op := match constr:(Set) with
                             | _ => constr:(Unop (var:=var) op)
                             | _ => constr:(Binop (var:=var) op)
                             | _ => constr:(Trinop (var:=var) op)
                             | _ => constr:(Trinop2Ret (var:=var) op)
                             end in
                   lazymatch op with
                   | Unop _ => lazymatch x with
                               | ?op' ?a
                                 => let a := reify var a in
                                    constr:(op a)
                               end
                   | Binop _ => lazymatch x with
                                | ?op' ?a ?b
                                  => let a := reify var a in
                                     let b := reify var b in
                                     constr:(op a b)
                                end
                   | Trinop _ => lazymatch x with
                                 | ?op' ?a ?b ?c
                                   => let a := reify var a in
                                      let b := reify var b in
                                      let c := reify var c in
                                      constr:(op a b c)
                                 end
                   | Trinop2Ret _ => lazymatch x with
                                     | ?op' ?a ?b ?c
                                       => let a := reify var a in
                                          let b := reify var b in
                                          let c := reify var c in
                                          constr:(op a b c)
                                     end
                   end
              end
         end
    end.
  Hint Extern 0 (reify ?var ?e) => (let e := reify var e in eexact e) : typeclass_instances.

  Ltac Reify e :=
    lazymatch constr:(fun (var:type->Type) => (_:reify var e)) with
      (fun var => ?C) => constr:(fun (var:type->Type) => C) (* copy the term but not the type cast *)
    end.

  Definition example_expr var : fancy_machine.W -> fancy_machine.W -> expr (var:=var) TW.
  Proof.
    intros x y.
    let f' := (eval cbv [f] in (f (x, y))) in
    let f' := (eval simpl in f') in
    let f' := (eval unfold fst', snd', fst, snd in f') in
    let rv := (reify var f') in exact rv.
  Defined.

  Lemma example_expr_good x y : Interp (fun var => @example_expr var x y) = f (x, y).
  Proof.
    cbv [Interp interp example_expr fst snd interp_nop].
    unfold f; simpl.
    reflexivity.
  Qed.

(*Ltac lhs_of_goal := match goal with |- ?R ?LHS ?RHS => constr:(LHS) end.
  Ltac rhs_of_goal := match goal with |- ?R ?LHS ?RHS => constr:(RHS) end.

  Ltac Reify_rhs :=
    let rhs := rhs_of_goal in
    let RHS := Reify rhs in
    transitivity (ZInterp RHS);
    [|cbv iota beta delta [ZInterp Interp interp_type interp_binop interp]; reflexivity].

  Goal (0 = let x := 1+2 in x*3)%Z.
    Reify_rhs.
  Abort.

  Goal (0 = let x := 1 in let y := 2 in x * y)%Z.
    Reify_rhs.
  Abort.

  Section wf.
    Context {T : Type} {var1 var2 : type -> Type}.

    Local Notation "x ≡ y" := (existT _ _ (x, y)).

    Definition Texpr var t := @expr T var t.

    Inductive wf : list (sigT (fun t => var1 t * var2 t))%type -> forall {t}, Texpr var1 t -> Texpr var2 t -> Prop :=
    | WfConst : forall G n, wf G (Const n) (Const n)
    | WfVar : forall G t x x', In (x ≡ x') G -> @wf G t (Var x) (Var x')
    | WfBinop : forall G {t1} {t2} (e1:Texpr var1 t1) (e2:Texpr var1 t2)
                       (e1':Texpr var2 t1) (e2':Texpr var2 t2) op,
        wf G e1 e1'
        -> wf G e2 e2'
        -> wf G (Binop (T := T) op e1 e2) (Binop (T := T) op e1' e2')
    | WfLet : forall G t1 t2 e1 e1' (e2 : _ t1 -> Texpr _ t2) e2',
        wf G e1 e1'
        -> (forall x1 x2, wf ((x1 ≡ x2) :: G) (e2 x1) (e2' x2))
        -> wf G (Let (T := T) e1 e2) (Let (T := T) e1' e2')
    | WfPair : forall G {t1} {t2} (e1: Texpr var1 t1) (e2: Texpr var1 t2)
                      (e1': Texpr var2 t1) (e2': Texpr var2 t2),
        wf G e1 e1'
        -> wf G e2 e2'
        -> wf G (Pair (T := T) e1 e2) (Pair (T := T) e1' e2')
    | WfMatchPair : forall G t1 t2 tC ep ep' (eC : _ t1 -> _ t2 -> Texpr _ tC) eC',
        wf G ep ep'
        -> (forall x1 x2 y1 y2, wf ((x1 ≡ x2) :: (y1 ≡ y2) :: G) (eC x1 y1) (eC' x2 y2))
        -> wf G (MatchPair (T := T) ep eC) (MatchPair (T := T) ep' eC').
  End wf.

  Definition Wf {T: Type} {t} (E : @Expr T t) := forall var1 var2, wf nil (E var1) (E var2).

  Example example_Expr_Wf : Wf example_Expr.
  Proof.
    unfold Wf; repeat match goal with
    | [ |- wf _ _ _ ] => constructor
    | [ |- In ?x (cons ?x _) ] => constructor 1; reflexivity
    | [ |- In _ _ ] => constructor 2
    | _ => intros
    end.
  Qed.

  Axiom Wf_admitted : forall {t} (E:Expr t), @Wf Z t E.
  Ltac admit_Wf := apply Wf_admitted.*)
End Input.

Module Output.

  Section Language.
    (* A very restricted language where binary operations are restricted
    to returning [T] and must appear in [let] binders, and all pairs
    must be constructed in the return clause.  No matching on pairs is
    allowed *)

    Section expr.
      Context {var : vartype -> Type}.

      Inductive arg : type -> Type :=
      | Const {t} : @interp_type (Tconst t) -> arg t
      | Var {t} : var t -> arg t
      | Pair : forall {t1}, arg t1 -> forall {t2}, arg t2 -> arg (Prod t1 t2).

      Inductive expr : type -> Type :=
      | LetUnop : forall {t1}, nop 1 1 t1 TW -> arg t1 ->
                               forall {tC}, (var TW -> expr tC) -> expr tC
      | LetBinop : forall {t1 t2}, nop 2 1 (t1, t2) TW -> arg t1 -> arg t2 ->
                                   forall {tC}, (var TW -> expr tC) -> expr tC
      | LetTrinop : forall {t1 t2 t3}, nop 3 1 (t1, t2, t3) TW -> arg t1 -> arg t2 -> arg t3 ->
                                       forall {tC}, (var TW -> expr tC) -> expr tC
      | LetTrinop2Ret : forall {t1 t2 t3}, nop 3 2 (t1, t2, t3) (Tvar Tbool, Tvar TW)
                                           -> arg t1 -> arg t2 -> arg t3 ->
                                           forall {tC}, (var Tbool -> var TW -> expr tC) -> expr tC
      | Return : forall {t}, arg t -> expr t.
    End expr.

    Arguments arg _ _ : clear implicits.
    Arguments expr _ _ : clear implicits.

    Definition Expr t : Type := forall var, expr var t.

    Fixpoint interp_arg {t} (e: arg interp_type t) : interp_type t :=
      match e with
      | Const _ n => n
      | Var _ n => n
      | Pair _ e1 _ e2 => (interp_arg e1, interp_arg e2)
      end.

    Fixpoint interp {t} (e:expr interp_type t) : interp_type t :=
      match e with
      | LetUnop _ op a _ eC
        => let x := interp_nop op (interp_arg a) in interp (eC x)
      | LetBinop _ _ op a b _ eC
        => let x := interp_nop op (interp_arg a, interp_arg b) in interp (eC x)
      | LetTrinop _ _ _ op a b c _ eC
        => let x := interp_nop op (interp_arg a, interp_arg b, interp_arg c) in interp (eC x)
      | LetTrinop2Ret _ _ _ op a b c _ eC
        => let '(c, v) := interp_nop op (interp_arg a, interp_arg b, interp_arg c) in interp (eC c v)
      | Return _ a => interp_arg a
      end.

    Definition Interp {t} (E:Expr t) : interp_type t := interp (E interp_type).
  End Language.

  Section under_lets.
    Context {var: vartype -> Type}.

    Arguments arg _ _ : clear implicits.
    Arguments expr _ _ : clear implicits.

    Fixpoint under_lets {t} (e: expr var t) {struct e} :
      forall {tC} (C:arg var t -> expr var tC), expr var tC
      := match e in (expr _ t) return forall {tC} (C:arg var t -> expr var tC), expr var tC with
         | LetUnop _ op a _ eC
           => fun tC C => LetUnop op a (fun v => @under_lets _ (eC v) _ C)
         | LetBinop _ _ op a b _ eC
           => fun tC C => LetBinop op a b (fun v => @under_lets _ (eC v) _ C)
         | LetTrinop _ _ _ op a b c _ eC
           => fun tC C => LetTrinop op a b c (fun v => @under_lets _ (eC v) _ C)
         | LetTrinop2Ret _ _ _ op a b c _ eC
           => fun tC C => LetTrinop2Ret op a b c (fun v0 v1 => @under_lets _ (eC v0 v1) _ C)
         | Return t a
           => fun _ C => C a
         end.
  End under_lets.

  (*Lemma under_lets_correct {t} (e: @expr T _ t) {tC}
    (C: @arg T _ t -> @expr T _ tC)
    (C_Proper : forall a1 a2, interp_arg a1 = interp_arg a2 -> interp (C a1) = interp (C a2)) :
    forall a, interp_arg a = interp e -> interp (under_lets e C) = interp (C a).
  Proof. induction e; repeat (intuition (congruence || eauto) + simpl + rewrite_hyp !* ). Qed.*)

  Section match_arg.
    Context {var:vartype -> Type}.

    Arguments arg _ _ : clear implicits.
    Arguments expr _ _ : clear implicits.

    Definition match_arg_Prod' {t1} {t2} (a:arg var (Prod t1 t2)) : option (arg var t1 * arg var t2) :=
      match a in arg _ t
        return option (match t with | Prod _ _ => _ | _ => False end) with
      | Pair _ a1 _ a2 => Some (a1, a2)
      | _ => None
      end.

    Definition match_arg_Prod {t1} {t2} (a:arg var (Prod t1 t2)) : (arg var t1 * arg var t2).
      refine match match_arg_Prod' a with
      | Some (a1, a2) => (a1, a2)
      | None => _ (* impossible *)
      end.
    Proof.
      intros; constructor;
        abstract (repeat match goal with
        | [a: interp_type _ |- _] => destruct a; constructor; assumption
        | [a: arg _ (Prod _ _) |- _] => inversion_clear a; try assumption
        end).
    Defined.

    Global Arguments match_arg_Prod / : simpl nomatch.

    Definition match_arg_Prod_Pair {t1 t2} (a1:arg var t1) (a2:arg var t2) :
      match_arg_Prod (Pair a1 a2) = (a1, a2) := eq_refl.

    Lemma match_arg_Prod_correct_helper {t} (a:arg var t) :
      match t return arg var t -> Prop with
      | Prod _ _ => fun a => forall a1 a2, match_arg_Prod a = (a1, a2) <-> a = Pair a1 a2
      | _ => fun _ => True
      end a.
    Proof.
      unfold match_arg_Prod; destruct a;
        repeat match goal with
        | _ => split
        | _ => intro
        | _ => progress simpl in *
        | _ => break_match
        | _ => intuition congruence
        | H: _ |- _ => eapply (f_equal match_arg_Prod) in H
        end.
    Qed.

    Lemma match_arg_Prod_correct {t1 t2} (a:arg _ (Prod t1 t2)) (a1:arg _ t1) (a2:arg _ t2) :
      match_arg_Prod a = (a1, a2) <-> a = (Pair a1 a2).
    Proof.
      pose proof (match_arg_Prod_correct_helper a) as H; simpl in H; rewrite H; reflexivity.
    Qed.

    Lemma Pair_eq t0 t1 x0 x1 x0' x1' : @Pair var t0 x0 t1 x1 = @Pair var t0 x0' t1 x1' <-> (x0, x1) = (x0', x1').
    Proof.
      split; intro H; try congruence.
      apply (f_equal match_arg_Prod) in H; assumption.
    Qed.
  End match_arg.

  Fixpoint uninterp_arg {t} {struct t} : interp_type t -> @arg interp_type t
    := match t return interp_type t -> @arg interp_type t with
       | Prod t1 t2 => fun x => let (x1, x2) := x in
                                Pair (@uninterp_arg t1 x1) (@uninterp_arg t2 x2)
       | TW => @Var interp_type _
       | Tbool => @Var interp_type _
       | TZ => Const
       end.

  Lemma interp_arg_uninterp_arg : forall t (a:interp_type t), interp_arg (uninterp_arg a) = a.
  Proof.
    induction t; simpl; intros; try reflexivity;
      break_match; subst; simpl; intuition congruence.
  Qed.

  Lemma interp_under_lets {t: type} {tC: type}
        (e: @expr _ t)
        (C: @arg _ t -> @expr _ tC)
        (C_Proper : forall a1 a2, interp_arg a1 = interp_arg a2 ->
              interp (C a1) = interp (C a2)) :
    interp (under_lets e C) = interp (C (@uninterp_arg t (interp e))).
  Proof.
    (*intros; apply under_lets_correct;
    [ assumption
    | rewrite interp_arg_uninterp_arg; reflexivity ].*)
  Admitted.
End Output.

Section compile.
  Context {ivar : type -> Type}.
  Context {ovar : type -> Type}.
  Context (make_ovar_W : fancy_machine.W -> ovar TW)
          (make_ovar_bool : bool -> ovar Tbool).

  Fixpoint reify_interped {t} : interp_type t -> @Output.expr ovar t
    := match t return interp_type t -> @Output.expr ovar t with
       | Prod t0 t1
         => fun x0x1
            => @Output.under_lets
                 _ _ (@reify_interped t0 (fst x0x1)) _
                 (fun x0
                  => @Output.under_lets
                       _ _ (@reify_interped t1 (snd x0x1)) _
                       (fun x1
                        => Output.Return (Output.Pair x0 x1)))
       | TZ => fun n => Output.Return (Output.Const n)
       | TW => fun n => Output.Return (Output.Var (make_ovar_W n))
       | Tbool => fun n => Output.Return (Output.Var (make_ovar_bool n))
       end.

  Fixpoint compile {t} (e:@Input.expr (@Output.arg ovar) t) : @Output.expr ovar t
    := match e in @Input.expr _ t return @Output.expr ovar t with
           | Input.Const _ n => reify_interped n
           | Input.Var _ n => Output.Return n
           | Input.Unop _ TW op a =>
             Output.under_lets (@compile _ a) (fun arg1 =>
                Output.LetUnop op arg1 (fun v => Output.Return (Output.Var v)))
           | Input.Unop _ _ op a => match op with OPldi => fun x => x end (* whee small inversion magic *)
           | Input.Binop _ _ TW op a b =>
             Output.under_lets (@compile _ a) (fun arg1 =>
             Output.under_lets (@compile _ b) (fun arg2 =>
                Output.LetBinop op arg1 arg2 (fun v => Output.Return (Output.Var v))))
           | Input.Binop _ _ _ op a b => match op with OPldi => fun x => x end (* whee small inversion magic *)
           | Input.Trinop _ _ _ TW op a b c =>
             Output.under_lets (@compile _ a) (fun arg1 =>
             Output.under_lets (@compile _ b) (fun arg2 =>
             Output.under_lets (@compile _ c) (fun arg3 =>
                Output.LetTrinop op arg1 arg2 arg3 (fun v => Output.Return (Output.Var v)))))
           | Input.Trinop _ _ _ _ op a b c => match op with OPldi => fun x => x end (* whee small inversion magic *)
           | Input.Trinop2Ret _ _ _ (Tbool, TW) op a b c =>
             Output.under_lets (@compile _ a) (fun arg1 =>
             Output.under_lets (@compile _ b) (fun arg2 =>
             Output.under_lets (@compile _ c) (fun arg3 =>
                Output.LetTrinop2Ret op arg1 arg2 arg3 (fun v0 v1 => Output.Return (Output.Pair (Output.Var v0) (Output.Var v1))))))
           | Input.Trinop2Ret _ _ _ _ op a b c => match op with OPldi => fun x => x end (* whee small inversion magic *)
    | Input.Let _ ex _ eC =>
       Output.under_lets (@compile _ ex) (fun arg => @compile _ (eC arg))
    | Input.Pair _ e1 _ e2 =>
       Output.under_lets (@compile _ e1) (fun arg1 =>
          Output.under_lets (@compile _ e2) (fun arg2 =>
             Output.Return (Output.Pair arg1 arg2)))
    | Input.MatchPair _ _ ep _ eC =>
        Output.under_lets (@compile _ ep) (fun arg =>
          let (a1, a2) := Output.match_arg_Prod arg in @compile _ (eC a1 a2))
           end.
  End compile.

(*Definition Compile {t} (e:Input.Expr t) : Output.Expr t := fun var =>
  compile (e (@Output.arg var)).*)

(*Lemma compile_correct {_: Evaluable Z} {t} e1 e2 G (wf:Input.wf G e1 e2) :
  List.Forall (fun v => let 'existT _ (x, a) := v in Output.interp_arg a = x) G ->
    Output.interp (compile e2) = Input.interp e1 :> interp_type t.
Proof.
  induction wf;
    repeat match goal with
    | [HIn:In ?x ?l, HForall:Forall _ ?l |- _ ] =>
      (pose proof (proj1 (Forall_forall _ _) HForall _ HIn); clear HIn)
    | [ H : Output.match_arg_Prod _ = (_, _) |- _ ] =>
      apply Output.match_arg_Prod_correct in H
    | [ H : Output.Pair _ _ = Output.Pair _ _ |- _ ] =>
      apply Output.Pair_eq in H
    | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
    | _ => progress intros
    | _ => progress simpl in *
    | _ => progress subst
    | _ => progress specialize_by assumption
    | _ => progress break_match
    | _ => rewrite !Output.interp_under_lets
    | _ => rewrite !Output.interp_arg_uninterp_arg
    | _ => progress erewrite_hyp !*
    | _ => apply Forall_cons
    | _ => solve [intuition (congruence || eauto)]
    end.
Qed.

Lemma Compile_correct {_: Evaluable Z} {t} (E:Input.Expr t) (WfE:Input.Wf E) :
  Output.Interp (Compile E) = Input.Interp E.
Proof. eapply compile_correct; eauto. Qed.
*)
Import Input.

Definition compiled_example (x y : fancy_machine.W) : Output.expr (var:=interp_type) TW
  := Eval vm_compute in @compile interp_type id id _ (example_expr _ x y).
Notation "'ilet' x := 'ldi' v 'in' b" :=
  (Output.LetUnop OPldi (Output.Const v) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'ldi'  v  'in' '//' b").
Notation "'ilet' x := 'mulhwll' A B 'in' b" :=
  (Output.LetBinop OPmulhwll (Output.Var A) (Output.Var B) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'mulhwll'  A  B  'in' '//' b").
Notation "'ilet' x := 'mulhwhl' A B 'in' b" :=
  (Output.LetBinop OPmulhwhl (Output.Var A) (Output.Var B) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'mulhwhl'  A  B  'in' '//' b").
Notation "'ilet' x := 'mulhwhh' A B 'in' b" :=
  (Output.LetBinop OPmulhwhh (Output.Var A) (Output.Var B) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'mulhwhh'  A  B  'in' '//' b").
Notation "'ilet' x := 'shl' A B 'in' b" :=
  (Output.LetBinop OPshl (Output.Var A) (Output.Const B) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'shl'  A  B  'in' '//' b").
Notation "'ilet' x := 'shr' A B 'in' b" :=
  (Output.LetBinop OPshr (Output.Var A) (Output.Const B) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'shr'  A  B  'in' '//' b").
Notation "'clet' ( c , x ) := 'adc' A B C 'in' b" :=
  (Output.LetTrinop2Ret OPadc (Output.Var A) (Output.Var B) (Output.Var C) (fun c x => b))
    (at level 200, b at level 200, format "'clet'  ( c ,  x )  :=  'adc'  A  B  C  'in' '//' b").
Notation "'clet' ( c , x ) := 'subc' A B C 'in' b" :=
  (Output.LetTrinop2Ret OPsubc (Output.Var A) (Output.Var B) (Output.Var C) (fun c x => b))
    (at level 200, b at level 200, format "'clet'  ( c ,  x )  :=  'subc'  A  B  C  'in' '//' b").
Notation "'clet' ( c , x ) := 'add' A B 'in' b" :=
  (Output.LetTrinop2Ret OPadc (Output.Var A) (Output.Var B) (Output.Var false) (fun c x => b))
    (at level 200, b at level 200, format "'clet'  ( c ,  x )  :=  'add'  A  B  'in' '//' b").
Notation "'clet' ( c , x ) := 'sub' A B 'in' b" :=
  (Output.LetTrinop2Ret OPsubc (Output.Var A) (Output.Var B) (Output.Var false) (fun c x => b))
    (at level 200, b at level 200, format "'clet'  ( c ,  x )  :=  'sub'  A  B  'in' '//' b").
Notation "'ilet' x := 'selc' A B C 'in' b" :=
  (Output.LetTrinop OPselc (Output.Var A) (Output.Var B) (Output.Var C) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'selc'  A  B  C  'in' '//' b").
Notation Return x := (Output.Return (Output.Var x)).
Print compiled_example.

(* compiled_example =
fun x y : fancy_machine.W =>
ilet x0 := ldi m' in
ilet x1 := mulhwll x x0 in
ilet x2 := ldi m' in
ilet x3 := mulhwhl x x2 in
ilet x4 := shl x3 128 in
clet (_, x6) := add x1 x4 in
ilet x7 := ldi m' in
ilet x8 := mulhwhl x7 x in
ilet x9 := shl x8 128 in
clet (_, x11) := add x6 x9 in
ilet x12 := ldi modulus in
ilet x13 := mulhwhh x11 x12 in
ilet x14 := ldi m' in
ilet x15 := mulhwll x x14 in
ilet x16 := ldi m' in
ilet x17 := mulhwhl x x16 in
ilet x18 := shl x17 128 in
clet (_, x20) := add x15 x18 in
ilet x21 := ldi m' in
ilet x22 := mulhwhl x21 x in
ilet x23 := shl x22 128 in
clet (_, x25) := add x20 x23 in
ilet x26 := ldi modulus in
ilet x27 := mulhwhl x25 x26 in
ilet x28 := shr x27 128 in
ilet x29 := ldi m' in
ilet x30 := mulhwll x x29 in
ilet x31 := ldi m' in
ilet x32 := mulhwhl x x31 in
ilet x33 := shl x32 128 in
clet (_, x35) := add x30 x33 in
ilet x36 := ldi m' in
ilet x37 := mulhwhl x36 x in
ilet x38 := shl x37 128 in
clet (_, x40) := add x35 x38 in
ilet x41 := ldi modulus in
ilet x42 := mulhwll x40 x41 in
ilet x43 := ldi m' in
ilet x44 := mulhwll x x43 in
ilet x45 := ldi m' in
ilet x46 := mulhwhl x x45 in
ilet x47 := shl x46 128 in
clet (_, x49) := add x44 x47 in
ilet x50 := ldi m' in
ilet x51 := mulhwhl x50 x in
ilet x52 := shl x51 128 in
clet (_, x54) := add x49 x52 in
ilet x55 := ldi modulus in
ilet x56 := mulhwhl x54 x55 in
ilet x57 := shl x56 128 in
clet (x58, _) := add x42 x57 in
clet (_, x61) := adc x13 x28 x58 in
ilet x62 := ldi modulus in
ilet x63 := ldi m' in
ilet x64 := mulhwll x x63 in
ilet x65 := ldi m' in
ilet x66 := mulhwhl x x65 in
ilet x67 := shl x66 128 in
clet (_, x69) := add x64 x67 in
ilet x70 := ldi m' in
ilet x71 := mulhwhl x70 x in
ilet x72 := shl x71 128 in
clet (_, x74) := add x69 x72 in
ilet x75 := mulhwhl x62 x74 in
ilet x76 := shr x75 128 in
ilet x77 := ldi m' in
ilet x78 := mulhwll x x77 in
ilet x79 := ldi m' in
ilet x80 := mulhwhl x x79 in
ilet x81 := shl x80 128 in
clet (_, x83) := add x78 x81 in
ilet x84 := ldi m' in
ilet x85 := mulhwhl x84 x in
ilet x86 := shl x85 128 in
clet (_, x88) := add x83 x86 in
ilet x89 := ldi modulus in
ilet x90 := mulhwll x88 x89 in
ilet x91 := ldi m' in
ilet x92 := mulhwll x x91 in
ilet x93 := ldi m' in
ilet x94 := mulhwhl x x93 in
ilet x95 := shl x94 128 in
clet (_, x97) := add x92 x95 in
ilet x98 := ldi m' in
ilet x99 := mulhwhl x98 x in
ilet x100 := shl x99 128 in
clet (_, x102) := add x97 x100 in
ilet x103 := ldi modulus in
ilet x104 := mulhwhl x102 x103 in
ilet x105 := shl x104 128 in
clet (_, x107) := add x90 x105 in
ilet x108 := ldi modulus in
ilet x109 := ldi m' in
ilet x110 := mulhwll x x109 in
ilet x111 := ldi m' in
ilet x112 := mulhwhl x x111 in
ilet x113 := shl x112 128 in
clet (_, x115) := add x110 x113 in
ilet x116 := ldi m' in
ilet x117 := mulhwhl x116 x in
ilet x118 := shl x117 128 in
clet (_, x120) := add x115 x118 in
ilet x121 := mulhwhl x108 x120 in
ilet x122 := shl x121 128 in
clet (x123, _) := add x107 x122 in
clet (_, x126) := adc x61 x76 x123 in
ilet x127 := ldi m' in
ilet x128 := mulhwll x x127 in
ilet x129 := ldi m' in
ilet x130 := mulhwhl x x129 in
ilet x131 := shl x130 128 in
clet (_, x133) := add x128 x131 in
ilet x134 := ldi m' in
ilet x135 := mulhwhl x134 x in
ilet x136 := shl x135 128 in
clet (_, x138) := add x133 x136 in
ilet x139 := ldi modulus in
ilet x140 := mulhwll x138 x139 in
ilet x141 := ldi m' in
ilet x142 := mulhwll x x141 in
ilet x143 := ldi m' in
ilet x144 := mulhwhl x x143 in
ilet x145 := shl x144 128 in
clet (_, x147) := add x142 x145 in
ilet x148 := ldi m' in
ilet x149 := mulhwhl x148 x in
ilet x150 := shl x149 128 in
clet (_, x152) := add x147 x150 in
ilet x153 := ldi modulus in
ilet x154 := mulhwhl x152 x153 in
ilet x155 := shl x154 128 in
clet (_, x157) := add x140 x155 in
ilet x158 := ldi modulus in
ilet x159 := ldi m' in
ilet x160 := mulhwll x x159 in
ilet x161 := ldi m' in
ilet x162 := mulhwhl x x161 in
ilet x163 := shl x162 128 in
clet (_, x165) := add x160 x163 in
ilet x166 := ldi m' in
ilet x167 := mulhwhl x166 x in
ilet x168 := shl x167 128 in
clet (_, x170) := add x165 x168 in
ilet x171 := mulhwhl x158 x170 in
ilet x172 := shl x171 128 in
clet (_, x174) := add x157 x172 in
clet (x175, _) := add x x174 in
clet (_, x178) := adc y x126 x175 in
ilet x179 := ldi m' in
ilet x180 := mulhwll x x179 in
ilet x181 := ldi m' in
ilet x182 := mulhwhl x x181 in
ilet x183 := shl x182 128 in
clet (_, x185) := add x180 x183 in
ilet x186 := ldi m' in
ilet x187 := mulhwhl x186 x in
ilet x188 := shl x187 128 in
clet (_, x190) := add x185 x188 in
ilet x191 := ldi modulus in
ilet x192 := mulhwhh x190 x191 in
ilet x193 := ldi m' in
ilet x194 := mulhwll x x193 in
ilet x195 := ldi m' in
ilet x196 := mulhwhl x x195 in
ilet x197 := shl x196 128 in
clet (_, x199) := add x194 x197 in
ilet x200 := ldi m' in
ilet x201 := mulhwhl x200 x in
ilet x202 := shl x201 128 in
clet (_, x204) := add x199 x202 in
ilet x205 := ldi modulus in
ilet x206 := mulhwhl x204 x205 in
ilet x207 := shr x206 128 in
ilet x208 := ldi m' in
ilet x209 := mulhwll x x208 in
ilet x210 := ldi m' in
ilet x211 := mulhwhl x x210 in
ilet x212 := shl x211 128 in
clet (_, x214) := add x209 x212 in
ilet x215 := ldi m' in
ilet x216 := mulhwhl x215 x in
ilet x217 := shl x216 128 in
clet (_, x219) := add x214 x217 in
ilet x220 := ldi modulus in
ilet x221 := mulhwll x219 x220 in
ilet x222 := ldi m' in
ilet x223 := mulhwll x x222 in
ilet x224 := ldi m' in
ilet x225 := mulhwhl x x224 in
ilet x226 := shl x225 128 in
clet (_, x228) := add x223 x226 in
ilet x229 := ldi m' in
ilet x230 := mulhwhl x229 x in
ilet x231 := shl x230 128 in
clet (_, x233) := add x228 x231 in
ilet x234 := ldi modulus in
ilet x235 := mulhwhl x233 x234 in
ilet x236 := shl x235 128 in
clet (x237, _) := add x221 x236 in
clet (_, x240) := adc x192 x207 x237 in
ilet x241 := ldi modulus in
ilet x242 := ldi m' in
ilet x243 := mulhwll x x242 in
ilet x244 := ldi m' in
ilet x245 := mulhwhl x x244 in
ilet x246 := shl x245 128 in
clet (_, x248) := add x243 x246 in
ilet x249 := ldi m' in
ilet x250 := mulhwhl x249 x in
ilet x251 := shl x250 128 in
clet (_, x253) := add x248 x251 in
ilet x254 := mulhwhl x241 x253 in
ilet x255 := shr x254 128 in
ilet x256 := ldi m' in
ilet x257 := mulhwll x x256 in
ilet x258 := ldi m' in
ilet x259 := mulhwhl x x258 in
ilet x260 := shl x259 128 in
clet (_, x262) := add x257 x260 in
ilet x263 := ldi m' in
ilet x264 := mulhwhl x263 x in
ilet x265 := shl x264 128 in
clet (_, x267) := add x262 x265 in
ilet x268 := ldi modulus in
ilet x269 := mulhwll x267 x268 in
ilet x270 := ldi m' in
ilet x271 := mulhwll x x270 in
ilet x272 := ldi m' in
ilet x273 := mulhwhl x x272 in
ilet x274 := shl x273 128 in
clet (_, x276) := add x271 x274 in
ilet x277 := ldi m' in
ilet x278 := mulhwhl x277 x in
ilet x279 := shl x278 128 in
clet (_, x281) := add x276 x279 in
ilet x282 := ldi modulus in
ilet x283 := mulhwhl x281 x282 in
ilet x284 := shl x283 128 in
clet (_, x286) := add x269 x284 in
ilet x287 := ldi modulus in
ilet x288 := ldi m' in
ilet x289 := mulhwll x x288 in
ilet x290 := ldi m' in
ilet x291 := mulhwhl x x290 in
ilet x292 := shl x291 128 in
clet (_, x294) := add x289 x292 in
ilet x295 := ldi m' in
ilet x296 := mulhwhl x295 x in
ilet x297 := shl x296 128 in
clet (_, x299) := add x294 x297 in
ilet x300 := mulhwhl x287 x299 in
ilet x301 := shl x300 128 in
clet (x302, _) := add x286 x301 in
clet (_, x305) := adc x240 x255 x302 in
ilet x306 := ldi m' in
ilet x307 := mulhwll x x306 in
ilet x308 := ldi m' in
ilet x309 := mulhwhl x x308 in
ilet x310 := shl x309 128 in
clet (_, x312) := add x307 x310 in
ilet x313 := ldi m' in
ilet x314 := mulhwhl x313 x in
ilet x315 := shl x314 128 in
clet (_, x317) := add x312 x315 in
ilet x318 := ldi modulus in
ilet x319 := mulhwll x317 x318 in
ilet x320 := ldi m' in
ilet x321 := mulhwll x x320 in
ilet x322 := ldi m' in
ilet x323 := mulhwhl x x322 in
ilet x324 := shl x323 128 in
clet (_, x326) := add x321 x324 in
ilet x327 := ldi m' in
ilet x328 := mulhwhl x327 x in
ilet x329 := shl x328 128 in
clet (_, x331) := add x326 x329 in
ilet x332 := ldi modulus in
ilet x333 := mulhwhl x331 x332 in
ilet x334 := shl x333 128 in
clet (_, x336) := add x319 x334 in
ilet x337 := ldi modulus in
ilet x338 := ldi m' in
ilet x339 := mulhwll x x338 in
ilet x340 := ldi m' in
ilet x341 := mulhwhl x x340 in
ilet x342 := shl x341 128 in
clet (_, x344) := add x339 x342 in
ilet x345 := ldi m' in
ilet x346 := mulhwhl x345 x in
ilet x347 := shl x346 128 in
clet (_, x349) := add x344 x347 in
ilet x350 := mulhwhl x337 x349 in
ilet x351 := shl x350 128 in
clet (_, x353) := add x336 x351 in
clet (x354, _) := add x x353 in
clet (x356, _) := adc y x305 x354 in
ilet x358 := ldi modulus in
ilet x359 := ldi 0 in
ilet x360 := selc x356 x358 x359 in
clet (_, x362) := sub x178 x360 in
Return x362
     : fancy_machine.W -> fancy_machine.W -> Output.expr TW
 *)
