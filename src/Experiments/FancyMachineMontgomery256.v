Require Import Coq.ZArith.ZArith.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.ArchitectureToZLike.
Require Import Crypto.BoundedArithmetic.ArchitectureToZLikeProofs.
Require Import Crypto.ModularArithmetic.Montgomery.ZBounded.
Require Import Crypto.Util.Tuple.
Require Import Coq.FSets.FMaps Coq.FSets.FMapAVL Coq.FSets.FMapFacts Coq.FSets.FMapFullAVL.

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
  Inductive consttype := TZ | Tvar (_ : vartype).
  Inductive type := Tconst (_ : consttype) | Prod : type -> type -> type.
  Global Coercion Tvar : vartype >-> consttype.
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
    Local Notation TW := (Tconst TW).
    Local Notation Tbool := (Tconst Tbool).
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

Inductive SpecialZConst : Set := Cmodulus | Cm'.
Fixpoint interp_SpecialZConst (e: SpecialZConst) : Z :=
  match e with Cmodulus => modulus | Cm' => m' end.

Module Input.
  Section Language.
    Section expr.
      Context {var : type -> Type}.

      Inductive expr : type -> Type :=
      | Const : forall {t}, interp_type t -> expr t
      | SpZConst : SpecialZConst -> expr TZ
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
      | SpZConst n => interp_SpecialZConst n
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
    | modulus => constr:(SpZConst (var := var) Cmodulus)
    | m' => constr:(SpZConst (var := var) Cm')
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

  Definition example_expr' var : forall (x y : fancy_machine.W) (xv yv : var (Tconst TW)), expr (var:=var) TW.
  Proof.
    intros x y xv yv.
    let f' := (eval cbv [f] in (f (x, y))) in
    let f' := (eval simpl in f') in
    let f' := (eval unfold fst', snd', fst, snd in f') in
    let rv := constr:(fun (_:reify_var_for_in_is x TW xv) (_:reify_var_for_in_is y TW yv) => (_ : reify var f')) in
    lazymatch rv with fun _ _ => ?rv => exact rv end.
  Defined.

  Definition example_expr var : forall (xv yv : var (Tconst TW)), expr (var:=var) TW.
  Proof.
    let f := (eval cbv beta delta [example_expr'] in (example_expr' var)) in
    lazymatch f with fun _ _ => ?rv => exact rv end.
  Defined.

  Lemma example_expr_good x y : interp (@example_expr _ x y) = f (x, y).
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
      | SpZConst : SpecialZConst -> arg TZ
      | Var {t} : var t -> arg t
      | Pair : forall {t1}, arg t1 -> forall {t2}, arg t2 -> arg (Prod t1 t2).

      Inductive expr : type -> Type :=
      | LetUnop : forall {t1}, nop 1 1 t1 TW -> arg t1 ->
                               forall {tC}, (var TW -> expr tC) -> expr tC
      | LetBinop : forall {t1 t2}, nop 2 1 (t1, t2) TW -> arg t1 -> arg t2 ->
                                   forall {tC}, (var TW -> expr tC) -> expr tC
      | LetTrinop : forall {t1 t2 t3}, nop 3 1 (t1, t2, t3) TW -> arg t1 -> arg t2 -> arg t3 ->
                                       forall {tC}, (var TW -> expr tC) -> expr tC
      | LetTrinop2Ret : forall {t1 t2 t3}, nop 3 2 (t1, t2, t3) (Tconst Tbool, Tconst TW)
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
      | SpZConst n => interp_SpecialZConst n
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
      repeat break_match; subst; simpl; intuition try congruence.
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
       | TW => fun n => Output.Return (Output.Const n)
       | Tbool => fun n => Output.Return (Output.Const n)
       end.

  Fixpoint compile {t} (e:@Input.expr (@Output.arg ovar) t) : @Output.expr ovar t
    := match e in @Input.expr _ t return @Output.expr ovar t with
           | Input.Const _ n => reify_interped n
           | Input.SpZConst n => Output.Return (Output.SpZConst n)
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

Section symbolic.
  Local Set Boolean Equality Schemes.
  Local Set Decidable Equality Schemes.
  (** Holds decidably-equal versions of raw expressions, for lookup. *)
  Inductive sop : Set :=
    SOPldi | SOPshrd | SOPshl | SOPshr | SOPmkl | SOPadc | SOPsubc | SOPmulhwll | SOPmulhwhl | SOPmulhwhh | SOPselc | SOPaddm.
  Inductive SymbolicExpr : Set :=
  | SConstZ : Z -> SymbolicExpr
  | SSpZConst : SpecialZConst -> SymbolicExpr
  | SConstBool : bool -> SymbolicExpr
  | SConstW : nat -> SymbolicExpr
  | SVar : vartype -> nat -> SymbolicExpr
  | SPair : SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  | SUnOp : sop -> SymbolicExpr -> SymbolicExpr
  | SBinOp : sop -> SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  | STrinOp : sop -> SymbolicExpr -> SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  | STrinOp2Ret : sop -> SymbolicExpr -> SymbolicExpr -> SymbolicExpr -> SymbolicExpr.
End symbolic.

Section CSE.
  Context {var : type -> Type}.
  Let svar t := (var t * SymbolicExpr)%type.
  Let mapping := (list (svar TW) * list (svar Tbool))%type.

  Fixpoint lookup' {t} (sv : SymbolicExpr) (xs : list (svar t)) {struct xs} : option (var t) :=
    match xs with
    | nil => None
    | (x, sv') :: xs' =>
      if SymbolicExpr_beq sv' sv
      then Some x
      else lookup' sv xs'
    end.
  Definition lookup t (sv : SymbolicExpr) (xs : mapping) : option (var t) :=
    match t with
    | TW => lookup' sv (fst xs)
    | Tbool => lookup' sv (snd xs)
    | _ => None
    end.
  Definition symbolicify_var {t : vartype} (v : var t) (xs : mapping) : SymbolicExpr :=
    SVar t (match t with
            | TW => length (fst xs)
            | Tbool => length (snd xs)
            end).
  Definition add_mapping {t} (v : var t) (sv : SymbolicExpr) (xs : mapping) : mapping :=
    match t return var t -> mapping with
    | TW => fun v => ((v, sv) :: fst xs, snd xs)
    | Tbool => fun v => (fst xs, (v, sv) :: snd xs)
    | _ => fun _ => xs
    end v.

  Fixpoint cseArg {t} (v : @Output.arg svar t) (xs : mapping) {struct v}
    : @Output.arg var t * option SymbolicExpr
    := match v in Output.arg t return Output.arg t * option SymbolicExpr with
       | Output.Const Tbool v'
         => let sv := SConstBool v' in
           (match lookup Tbool sv xs with
            | Some val => Output.Var val
            | None => Output.Const v'
            end,
            Some sv)
       | Output.Const TZ v'
         => (Output.Const v', Some (SConstZ v'))
       | Output.SpZConst v'
         => (Output.SpZConst v', Some (SSpZConst v'))
       | Output.Const _ v' => (Output.Const v', None)
       | Output.Var t v'
         => (Output.Var (match lookup t (snd v') xs with
                        | Some val => val
                        | None => fst v'
                        end),
            Some (snd v'))
       | Output.Pair _ v0 _ v1
         => let '(v0v, v0s) := eta (@cseArg _ v0 xs) in
           let '(v1v, v1s) := eta (@cseArg _ v1 xs) in
           (Output.Pair v0v v1v,
            match v0s, v1s with
            | Some v0', Some v1' => Some (SPair v0' v1')
            | _, _ => None
            end)
       end.
  Definition cseOp {narg nret t1 t2} (op : @nop narg nret t1 t2) : sop
    := match op with
       | OPldi => SOPldi
       | OPshrd => SOPshrd
       | OPshl => SOPshl
       | OPshr => SOPshr
       | OPmkl => SOPmkl
       | OPadc => SOPadc
       | OPsubc => SOPsubc
       | OPmulhwll => SOPmulhwll
       | OPmulhwhl => SOPmulhwhl
       | OPmulhwhh => SOPmulhwhh
       | OPselc => SOPselc
       | OPaddm => SOPaddm
       end.

  Definition cseExprHelper1
             (cseExpr : forall t (v : @Output.expr svar t) (xs : mapping), @Output.expr var t)
             (xs : mapping)
             {tC}
             (f : svar TW -> @Output.expr svar tC)
             (sv : option SymbolicExpr)
             (default_head : (var TW -> @Output.expr var tC) -> @Output.expr var tC)
    : @Output.expr var tC
    := match option_map (fun sv' => (sv', lookup _ sv' xs)) sv with
       | Some (sv', Some v') => @cseExpr _ (f (v', sv')) xs
       | Some (sv', None)    => default_head (fun v => @cseExpr _ (f (v, sv')) (add_mapping v sv' xs))
       | None                => default_head (fun v => let sv' := symbolicify_var v xs in
                                                       @cseExpr _ (f (v, sv')) (add_mapping v sv' xs))
       end.
  Definition cseExprHelper2
             (cseExpr : forall t (v : @Output.expr svar t) (xs : mapping), @Output.expr var t)
             (xs : mapping)
             {tC}
             (f : svar Tbool -> svar TW -> @Output.expr svar tC)
             (sv : option SymbolicExpr)
             (default_head : (var Tbool -> var TW -> @Output.expr var tC) -> @Output.expr var tC)
    : @Output.expr var tC
    := match option_map (fun sv' => (sv', lookup Tbool sv' xs, lookup TW sv' xs)) sv with
       | Some (sv', Some vb', Some vw')
         => @cseExpr _ (f (vb', sv') (vw', sv')) xs
       | Some (sv', _, _)
         => default_head (fun vb vw => @cseExpr _ (f (vb, sv') (vw, sv'))
                                                (add_mapping vw sv' (add_mapping vb sv' xs)))
       | None
         => default_head (fun vb vw => let svb' := symbolicify_var vb xs in
                                       let svw' := symbolicify_var vw xs in
                                       @cseExpr _ (f (vb, svb') (vw, svw'))
                                                (add_mapping vw svw' (add_mapping vb svb' xs)))
       end.
  Definition cseExpr_step
             (cseExpr : forall {t} (v : @Output.expr svar t) (xs : mapping), @Output.expr var t)
             {t} (v : @Output.expr svar t) (xs : mapping)
    : @Output.expr var t
    := match v in Output.expr t return Output.expr t with
       | Output.LetUnop _ op x0 _ f
         => let sop := cseOp op in
            let '(x0v, x0s) := eta (cseArg x0 xs) in
            let sv := match x0s with
                      | Some x0' => Some (SUnOp sop x0')
                      | _ => None
                      end in
            let default_head := Output.LetUnop op x0v in
            cseExprHelper1 (@cseExpr) xs f sv default_head
       | Output.LetBinop _ _ op x0 x1 _ f
         => let sop := cseOp op in
            let '(x0v, x0s) := eta (cseArg x0 xs) in
            let '(x1v, x1s) := eta (cseArg x1 xs) in
            let sv := match x0s, x1s with
                      | Some x0', Some x1' => Some (SBinOp sop x0' x1')
                      | _, _ => None
                      end in
            let default_head := Output.LetBinop op x0v x1v in
            cseExprHelper1 (@cseExpr) xs f sv default_head
       | Output.LetTrinop _ _ _ op x0 x1 x2 _ f
         => let sop := cseOp op in
            let '(x0v, x0s) := eta (cseArg x0 xs) in
            let '(x1v, x1s) := eta (cseArg x1 xs) in
            let '(x2v, x2s) := eta (cseArg x2 xs) in
            let sv := match x0s, x1s, x2s with
                      | Some x0', Some x1', Some x2' => Some (STrinOp sop x0' x1' x2')
                      | _, _, _ => None
                      end in
            let default_head := Output.LetTrinop op x0v x1v x2v in
            cseExprHelper1 (@cseExpr) xs f sv default_head
       | Output.LetTrinop2Ret _ _ _ op x0 x1 x2 _ f
         => let sop := cseOp op in
            let '(x0v, x0s) := eta (cseArg x0 xs) in
            let '(x1v, x1s) := eta (cseArg x1 xs) in
            let '(x2v, x2s) := eta (cseArg x2 xs) in
            let sv := match x0s, x1s, x2s with
                      | Some x0', Some x1', Some x2' => Some (STrinOp2Ret sop x0' x1' x2')
                      | _, _, _ => None
                      end in
            let default_head := Output.LetTrinop2Ret op x0v x1v x2v in
            cseExprHelper2 (@cseExpr) xs f sv default_head
       | Output.Return _ x => Output.Return (fst (cseArg x xs))
       end.
End CSE.
Fixpoint cseExpr {var t} v xs := @cseExpr_step var (@cseExpr var) t v xs.

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


Section syn.
  Context {var : vartype -> Type}.
  Inductive Syntax :=
  | RegPInv
  | RegMod
  | RegZero
  | cLowerHalf : Syntax -> Syntax
  | cUpperHalf : Syntax -> Syntax
  | cLeftShifted : Syntax -> Z -> Syntax
  | cRightShifted : Syntax -> Z -> Syntax
  | cVar : var TW -> Syntax
  | cVarC : var Tbool -> Syntax
  | cBind : Syntax -> (var TW -> Syntax) -> Syntax
  | cBindCarry : Syntax -> (var Tbool -> var TW -> Syntax) -> Syntax
  | cMul128 : Syntax -> Syntax -> Syntax
  | cSelc : var Tbool -> Syntax -> Syntax -> Syntax
  | cAddc : var Tbool -> Syntax -> Syntax -> Syntax
  | cAdd : Syntax -> Syntax -> Syntax
  | cSub : Syntax -> Syntax -> Syntax
  | cPair : Syntax -> Syntax -> Syntax
  | cINVALID {T} (_ : T).
End syn.

Fixpoint assemble_arg {var} {t} (v : @Output.arg (fun _ => @Syntax var) t) : @Syntax var
  := match v with
     | Output.Const TZ v' => if Z_beq v' 0 then RegZero else cINVALID v'
     | Output.Const _ x => cINVALID x
     | Output.SpZConst Cm' => RegPInv
     | Output.SpZConst Cmodulus => RegMod
     | Output.Var _ v => v
     | Output.Pair _ x0 _ x1 => cPair (@assemble_arg _ _ x0) (@assemble_arg _ _ x1)
     end.
Definition var_of_arg_helper {var} {t} (v : @Output.arg var t)
  : match t with
    | Prod _ _ => unit
    | Tconst t'
      => match t' with
         | Tvar t'' => var t''
         | TZ => SpecialZConst
         end + interp_type t'
    end.
Proof.
  destruct v;
    try solve [ right; assumption
              | left; assumption
              | exact tt ].
Defined.

Definition assemble_syntax_step
           (assemble_syntax : forall {var} {t} (v : @Output.expr (fun _ => @Syntax var) t), @Syntax var)
           {var} {t} (v : @Output.expr (fun _ => @Syntax var) t) : @Syntax var.
Proof.
  refine match v with
         | Output.LetUnop _ op x0 _ b
           => let x0' := assemble_arg x0 in
              match op with
              | OPldi => @assemble_syntax var _ (b x0')
              | _ => cINVALID op
              end
         | Output.LetBinop _ _ op x0 x1 _ b
           => let x0' : @Syntax var := assemble_arg x0 in
              let x1' : @Syntax var := assemble_arg x1 in
              let default := fun s => cBind s (fun v => @assemble_syntax var _ (b (cVar v))) in
              match op, x1 return @Syntax var with
              | OPshl, Output.Const TZ x1'
                => @assemble_syntax var _ (b (cLeftShifted x0' x1'))
              | OPshr, Output.Const TZ x1'
                => @assemble_syntax var _ (b (cRightShifted x0' x1'))
              | OPmulhwll, _
                => default (cMul128 (cLowerHalf x0') (cLowerHalf x1'))
              | OPmulhwhl, _
                => default (cMul128 (cUpperHalf x0') (cLowerHalf x1'))
              | OPmulhwhh, _
                => default (cMul128 (cUpperHalf x0') (cUpperHalf x1'))
              | _, _ => default (cINVALID op)
              end
         | Output.LetTrinop _ _ _ op x0 x1 x2 _ b
           => let x0' : @Syntax var := assemble_arg x0 in
              let x1' : @Syntax var := assemble_arg x1 in
              let x2' : @Syntax var := assemble_arg x2 in
              cBind (match op, x0', x2', x2 return @Syntax var with
                     | OPadc, _, _, Output.Const Tbool false
                       => cAdd x0' x1'
                     | OPadc, _, cVarC x2', _
                       => cAddc x2' x0' x1'
                     | OPsubc, _, _, Output.Const Tbool false
                       => cSub x0' x1'
                     | OPselc, cVarC x0', _, _
                       => cSelc x0' x1' x2'
                     | _, _, _, _ => cINVALID op
                     end)
                    (fun v => @assemble_syntax var _ (b (cVar v)))
         | Output.LetTrinop2Ret _ _ _ op x0 x1 x2 _ b
           => let x0' : @Syntax var := assemble_arg x0 in
              let x1' : @Syntax var := assemble_arg x1 in
              let x2' : @Syntax var := assemble_arg x2 in
              cBindCarry (match op, x0', x2', x2 return @Syntax var with
                          | OPadc, _, _, Output.Const Tbool false
                            => cAdd x0' x1'
                          | OPadc, _, cVarC x2', _
                            => cAddc x2' x0' x1'
                          | OPsubc, _, _, Output.Const Tbool false
                            => cSub x0' x1'
                          | _, _, _, _ => cINVALID op
                          end)
                         (fun c v => @assemble_syntax var _ (b (cVarC c) (cVar v)))
         | Output.Return _ x => @assemble_arg var _ x
         end.
  exact (fun _ => unit).
Defined.
Fixpoint assemble_syntax {var} {t} (v : @Output.expr (fun _ => @Syntax var) t) : @Syntax var
  := @assemble_syntax_step (@assemble_syntax) var t v.

Import Input.

Notation "'ilet' x := 'ldi' v 'in' b" :=
  (Output.LetUnop OPldi (Output.Const v) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'ldi'  v  'in' '//' b").
Notation "'ilet' x := 'ldi' 'm'' 'in' b" :=
  (Output.LetUnop OPldi (Output.SpZConst Cm') (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'ldi'  'm''  'in' '//' b").
Notation "'ilet' x := 'ldi' 'modulus' 'in' b" :=
  (Output.LetUnop OPldi (Output.SpZConst Cmodulus) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'ldi'  'modulus'  'in' '//' b").
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
  (Output.LetTrinop2Ret OPadc (Output.Var A) (Output.Var B) (Output.Const false) (fun c x => b))
    (at level 200, b at level 200, format "'clet'  ( c ,  x )  :=  'add'  A  B  'in' '//' b").
Notation "'clet' ( c , x ) := 'sub' A B 'in' b" :=
  (Output.LetTrinop2Ret OPsubc (Output.Var A) (Output.Var B) (Output.Const false) (fun c x => b))
    (at level 200, b at level 200, format "'clet'  ( c ,  x )  :=  'sub'  A  B  'in' '//' b").
Notation "'ilet' x := 'selc' A B C 'in' b" :=
  (Output.LetTrinop OPselc (Output.Var A) (Output.Var B) (Output.Var C) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'selc'  A  B  C  'in' '//' b").
Notation Return x := (Output.Return (Output.Var x)).

Definition compiled_example (x y : fancy_machine.W) : Output.expr (var:=interp_type) TW
  := Eval vm_compute in
      let x := (x, SVar TW 0)%core in
      let y := (y, SVar TW 1)%core in
      @cseExpr interp_type _
               (ilet RegZero := ldi (0 : interp_type TZ) in
                ilet RegMod := ldi modulus in
                ilet RegPinv := ldi m' in
                @compile _ _ (example_expr _ (Output.Var x) (Output.Var y)))
               (y::x::nil, nil).
Definition compiled_example_syn (x y : fancy_machine.W) : Syntax (var:=interp_type)
  := Eval vm_compute in
      assemble_syntax
        (let x := (cVar x, SVar TW 0)%core in
         let y := (cVar y, SVar TW 1)%core in
         @cseExpr (fun _ => @Syntax interp_type) _
                  (ilet RegZero := ldi (0 : interp_type TZ) in
                   ilet RegMod := ldi modulus in
                   ilet RegPinv := ldi m' in
                   @compile _ _ (example_expr _ (Output.Var x) (Output.Var y)))
                  (y::x::nil, nil)).
Print compiled_example.


(* compiled_example =
fun x y : fancy_machine.W =>
ilet x0 := ldi m' in
ilet x1 := mulhwll x x0 in
ilet x2 := mulhwhl x x0 in
ilet x3 := shl x2 128 in
clet (_, x5) := add x1 x3 in
ilet x6 := mulhwhl x0 x in
ilet x7 := shl x6 128 in
clet (_, x9) := add x5 x7 in
ilet x10 := ldi modulus in
ilet x11 := mulhwhh x9 x10 in
ilet x12 := mulhwhl x9 x10 in
ilet x13 := shr x12 128 in
ilet x14 := mulhwll x9 x10 in
ilet x15 := shl x12 128 in
clet (x16, x17) := add x14 x15 in
clet (_, x19) := adc x11 x13 x16 in
ilet x20 := mulhwhl x10 x9 in
ilet x21 := shr x20 128 in
ilet x22 := shl x20 128 in
clet (x23, x24) := add x17 x22 in
clet (_, x26) := adc x19 x21 x23 in
clet (x27, _) := add x x24 in
clet (x29, x30) := adc y x26 x27 in
ilet x31 := ldi 0 in
ilet x32 := selc x29 x10 x31 in
clet (_, x34) := sub x30 x32 in
Return x34
     : fancy_machine.W -> fancy_machine.W -> Output.expr TW
 *)


Notation "'ilet' x := 'ldi' v 'in' b" :=
  (Output.LetUnop OPldi (Output.Const v) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'ldi'  v  'in' '//' b").
Notation "'ilet' x := 'ldi' 'm'' 'in' b" :=
  (Output.LetUnop OPldi (Output.SpZConst Cm') (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'ldi'  'm''  'in' '//' b").
Notation "'ilet' x := 'ldi' 'modulus' 'in' b" :=
  (Output.LetUnop OPldi (Output.SpZConst Cmodulus) (fun x => b))
    (at level 200, b at level 200, format "'ilet'  x  :=  'ldi'  'modulus'  'in' '//' b").
Notation "'c.Mul128' ( x , 'c.LowerHalf' ( A ) , 'c.LowerHalf' ( B ) ) , b" :=
  (Output.LetBinop OPmulhwll (Output.Var A) (Output.Var B) (fun x => b))
    (at level 200, b at level 200, A at level 0, B at level 0, format "'c.Mul128' ( x ,  'c.LowerHalf' ( A ) ,  'c.LowerHalf' ( B ) ) , '//' b").
Notation "'c.Mul128' ( x , 'c.UpperHalf' ( A ) , 'c.LowerHalf' ( B ) ) , b" :=
  (Output.LetBinop OPmulhwhl (Output.Var A) (Output.Var B) (fun x => b))
    (at level 200, b at level 200, A at level 0, B at level 0, format "'c.Mul128' ( x ,  'c.UpperHalf' ( A ) ,  'c.LowerHalf' ( B ) ) , '//' b").
Notation "'c.Mul128' ( x , 'c.UpperHalf' ( A ) , 'c.UpperHalf' ( B ) ) , b" :=
  (Output.LetBinop OPmulhwhh (Output.Var A) (Output.Var B) (fun x => b))
    (at level 200, b at level 200, A at level 0, B at level 0, format "'c.Mul128' ( x ,  'c.UpperHalf' ( A ) ,  'c.UpperHalf' ( B ) ) , '//' b").
Notation "'let' x := 'c.LeftShifted' { A , B } 'in' b" :=
  (Output.LetBinop OPshl (Output.Var A) (Output.Const B) (fun x => b))
    (at level 200, b at level 200, format "'let'  x  :=  'c.LeftShifted' { A ,  B }  'in' '//' b").
Notation "'let' x := 'c.RightShifted' { A , B } 'in' b" :=
  (Output.LetBinop OPshr (Output.Var A) (Output.Const B) (fun x => b))
    (at level 200, b at level 200, format "'let'  x  :=  'c.RightShifted' { A ,  B }  'in' '//' b").
Notation "'clet' ( c , x ) := 'adc' A B C 'in' b" :=
  (Output.LetTrinop2Ret OPadc (Output.Var A) (Output.Var B) (Output.Var C) (fun c x => b))
    (at level 200, b at level 200, format "'clet'  ( c ,  x )  :=  'adc'  A  B  C  'in' '//' b").
Notation "'clet' ( c , x ) := 'subc' A B C 'in' b" :=
  (Output.LetTrinop2Ret OPsubc (Output.Var A) (Output.Var B) (Output.Var C) (fun c x => b))
    (at level 200, b at level 200, format "'clet'  ( c ,  x )  :=  'subc'  A  B  C  'in' '//' b").
Notation "'clet' ( c , x ) := 'add' A B 'in' b" :=
  (Output.LetTrinop2Ret OPadc (Output.Var A) (Output.Var B) (Output.Const false) (fun c x => b))
    (at level 200, b at level 200, format "'clet'  ( c ,  x )  :=  'add'  A  B  'in' '//' b").

Notation "'c.Add' ( x , A , B ) , b" :=
  (Output.LetTrinop2Ret OPadc (Output.Var A) (Output.Var B) (Output.Const false) (fun _ x => b))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' b").

Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x' , A' , B' ) , b" :=
  (Output.LetTrinop2Ret OPadc (Output.Var A) (Output.Var B) (Output.Const false) (fun c x => (Output.LetTrinop2Ret OPadc (Output.Var A') (Output.Var B') (Output.Var c) (fun _ x' => b))))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x' ,  A' ,  B' ) , '//' b").

Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x' , A' , B' ) , 'c.Selc' ( x'' , A'' , B'' ) , b" :=
  (Output.LetTrinop2Ret OPadc (Output.Var A) (Output.Var B) (Output.Const false) (fun c x => (Output.LetTrinop2Ret OPadc (Output.Var A') (Output.Var B') (Output.Var c) (fun c' x' => (Output.LetTrinop OPselc (Output.Var c') (Output.Var A'') (Output.Var B'') (fun x'' => b))))))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x' ,  A' ,  B' ) , '//' 'c.Selc' ( x'' ,  A'' ,  B'' ) , '//' b").

Notation "'c.Sub' ( x , A , B ) , b" :=
  (Output.LetTrinop2Ret OPsubc (Output.Var A) (Output.Var B) (Output.Const false) (fun _ x => b))
    (at level 200, b at level 200, format "'c.Sub' ( x ,  A ,  B ) , '//' b").
Print compiled_example.

(* compiled_example =
fun x y : fancy_machine.W =>
ilet x0 := ldi 0 in
ilet x1 := ldi modulus in
ilet x2 := ldi m' in
c.Mul128(x3, c.LowerHalf(x), c.LowerHalf(x2)),
c.Mul128(x4, c.UpperHalf(x), c.LowerHalf(x2)),
let x5 := c.LeftShifted{x4, 128} in
c.Add(x7, x3, x5),
c.Mul128(x8, c.UpperHalf(x2), c.LowerHalf(x)),
let x9 := c.LeftShifted{x8, 128} in
c.Add(x11, x7, x9),
c.Mul128(x12, c.UpperHalf(x11), c.UpperHalf(x1)),
c.Mul128(x13, c.UpperHalf(x11), c.LowerHalf(x1)),
let x14 := c.RightShifted{x13, 128} in
c.Mul128(x15, c.LowerHalf(x11), c.LowerHalf(x1)),
let x16 := c.LeftShifted{x13, 128} in
c.Add(x18, x15, x16),
c.Addc(x20, x12, x14),
c.Mul128(x21, c.UpperHalf(x1), c.LowerHalf(x11)),
let x22 := c.RightShifted{x21, 128} in
let x23 := c.LeftShifted{x21, 128} in
c.Add(x25, x18, x23),
c.Addc(x27, x20, x22),
c.Add(_, x, x25),
c.Addc(x31, y, x27),
c.Selc(x32, x1, x0),
c.Sub(x34, x31, x32),
Return x34
     : fancy_machine.W -> fancy_machine.W -> Output.expr TW
 *)

Notation "'Return' x" := (cVar x) (at level 200).
Notation "'c.Mul128' ( x , A , B ) , b" :=
  (cBind (cMul128 A B) (fun x => b))
    (at level 200, b at level 200, format "'c.Mul128' ( x ,  A ,  B ) , '//' b").
Notation "'c.Add' ( x , A , B ) , b" :=
  (cBindCarry (cAdd A B) (fun _ x => b))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' b").
Notation "'c.Add' ( x , A , B ) , b" :=
  (cBindCarry (cAdd (cVar A) B) (fun _ x => b))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , b" :=
  (cBindCarry (cAdd A B) (fun c x => cBindCarry (cAddc c A1 B1) (fun _ x1 => b)))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , b" :=
  (cBindCarry (cAdd A B) (fun c x => cBindCarry (cAddc c (cVar A1) B1) (fun _ x1 => b)))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , b" :=
  (cBindCarry (cAdd (cVar A) B) (fun c x => cBindCarry (cAddc c A1 B1) (fun _ x1 => b)))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , b" :=
  (cBindCarry (cAdd (cVar A) B) (fun c x => cBindCarry (cAddc c (cVar A1) B1) (fun _ x1 => b)))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , 'c.Selc' ( x2 , A2 , B2 ) , b" :=
  (cBindCarry (cAdd A B) (fun c x => cBindCarry (cAddc c A1 B1) (fun c1 x1 => cBind (cSelc c1 A2 B2) (fun x2 => b))))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' 'c.Selc' ( x2 ,  A2 ,  B2 ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , 'c.Selc' ( x2 , A2 , B2 ) , b" :=
  (cBindCarry (cAdd (cVar A) B) (fun c x => cBindCarry (cAddc c A1 B1) (fun c1 x1 => cBind (cSelc c1 A2 B2) (fun x2 => b))))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' 'c.Selc' ( x2 ,  A2 ,  B2 ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , 'c.Selc' ( x2 , A2 , B2 ) , b" :=
  (cBindCarry (cAdd A B) (fun c x => cBindCarry (cAddc c (cVar A1) B1) (fun c1 x1 => cBind (cSelc c1 A2 B2) (fun x2 => b))))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' 'c.Selc' ( x2 ,  A2 ,  B2 ) , '//' b").
Notation "'c.Add' ( x , A , B ) , 'c.Addc' ( x1 , A1 , B1 ) , 'c.Selc' ( x2 , A2 , B2 ) , b" :=
  (cBindCarry (cAdd (cVar A) B) (fun c x => cBindCarry (cAddc c (cVar A1) B1) (fun c1 x1 => cBind (cSelc c1 A2 B2) (fun x2 => b))))
    (at level 200, b at level 200, format "'c.Add' ( x ,  A ,  B ) , '//' 'c.Addc' ( x1 ,  A1 ,  B1 ) , '//' 'c.Selc' ( x2 ,  A2 ,  B2 ) , '//' b").

Notation "'c.Sub' ( x , A , B ) , b" :=
  (cBindCarry (cSub A B) (fun _ x => b))
    (at level 200, b at level 200, format "'c.Sub' ( x ,  A ,  B ) , '//' b").
Notation "'c.Sub' ( x , A , B ) , b" :=
  (cBindCarry (cSub (cVar A) B) (fun _ x => b))
    (at level 200, b at level 200, format "'c.Sub' ( x ,  A ,  B ) , '//' b").

Notation "'c.LowerHalf' ( x )" :=
  (cLowerHalf x)
    (at level 200, format "'c.LowerHalf' ( x )").
Notation "'c.LowerHalf' ( x )" :=
  (cLowerHalf (cVar x))
    (at level 200, format "'c.LowerHalf' ( x )").
Notation "'c.UpperHalf' ( x )" :=
  (cUpperHalf x)
    (at level 200, format "'c.UpperHalf' ( x )").
Notation "'c.UpperHalf' ( x )" :=
  (cUpperHalf (cVar x))
    (at level 200, format "'c.UpperHalf' ( x )").
Notation "'c.LeftShifted' { x , v }" :=
  (cLeftShifted x v)
    (at level 200, format "'c.LeftShifted' { x ,  v }").
Notation "'c.LeftShifted' { x , v }" :=
  (cLeftShifted (cVar x) v)
    (at level 200, format "'c.LeftShifted' { x ,  v }").
Notation "'c.RightShifted' { x , v }" :=
  (cRightShifted x v)
    (at level 200, format "'c.RightShifted' { x ,  v }").
Notation "'c.RightShifted' { x , v }" :=
  (cRightShifted (cVar x) v)
    (at level 200, format "'c.RightShifted' { x ,  v }").
Print compiled_example_syn.
