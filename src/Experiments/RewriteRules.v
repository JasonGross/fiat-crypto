Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.LetIn.
Import ListNotations.

Set Boolean Equality Schemes.
Inductive ctor : nat -> Set :=
| O : ctor 0
| S : ctor 1
| Add : ctor 2.

Definition arg_count {n} (_ : ctor n) := n.

Fixpoint ctor_beq_cps {T n m} (X : ctor n) (Y : ctor m) (k : bool -> T) {struct X} : T
  := match X, Y with
     | O, O
     | S, S
     | Add, Add
       => k true
     | O, _
     | S, _
     | Add, _
       => k false
     end.

Inductive expr :=
| AppCtor {n} (c : ctor n) (args : list expr)
| Literal (n : nat).

Inductive pattern :=
| Wildcard
| pLiteral
| pCtor {n} (c : ctor n) (args : list pattern).

Delimit Scope expr_scope with expr.
Bind Scope expr_scope with expr.
Notation "0" := (AppCtor O nil) : expr_scope.
Notation "n '.+1'" := (AppCtor S (n%expr :: nil)) (at level 10, format "n '.+1'") : expr_scope.
Notation "x + y" := (AppCtor Add (x%expr :: y%expr :: nil)) : expr_scope.
Notation "# n" := (Literal n) : expr_scope.

Delimit Scope pattern_scope with pattern.
Bind Scope pattern_scope with pattern.
Notation "0" := (pCtor O nil) : pattern_scope.
Notation "n '.+1'" := (pCtor S (n%pattern :: nil)) (at level 10, format "n '.+1'") : pattern_scope.
Notation "x + y" := (pCtor Add (x%pattern :: y%pattern :: nil)) : pattern_scope.
Notation "#?" := pLiteral : pattern_scope.
Notation "??" := Wildcard : pattern_scope.

Definition hlist {A} (f : A -> Set) (ls : list A)
  := fold_right
       (fun a b : Set => prod a b)
       unit
       (map f ls).

Fixpoint binding_dataT (p : pattern)
  := match p with
     | Wildcard => expr
     | pLiteral => nat
     | pCtor _ _ args
       => hlist binding_dataT args
     end.

Fixpoint bind_data_cps {T} (e : expr) (p : pattern)
  : (option (binding_dataT p) -> T) -> T
  := match p return (option (binding_dataT p) -> T) -> T with
     | Wildcard => fun k => k (Some e)
     | pLiteral
       => fun k
          => match e with
             | Literal n => k (Some n)
             | _ => k None
             end
     | pCtor _ c args
       => fun k
          => match e with
             | AppCtor _ c' args'
               => ctor_beq_cps
                    c c'
                    (fun b
                     => if b
                        then list_rect
                               (fun args => list expr -> (option (hlist binding_dataT args) -> T) -> T)
                               (fun args' k
                                => match args' with
                                   | nil => k (Some tt)
                                   | cons _ _ => k None
                                   end)
                               (fun p0 ps bind_data_rest args' k
                                => match args' with
                                   | nil => k None
                                   | e0 :: es
                                     => @bind_data_cps
                                          T e0 p0
                                          (fun v0
                                           => bind_data_rest
                                                es
                                                (fun vs
                                                 => k (v0 <- v0; vs <- vs; Some (v0, vs))))
                                   end)
                               args
                               args'
                               k
                        else k None)
             | _ => k None
             end
     end%option.

Fixpoint domatch (ps : list { p : pattern & binding_dataT p -> option expr })
         (e : expr)
  : expr
  := match ps with
     | nil => e
     | existT p f :: ps
       => let default _ := domatch ps e in
          bind_data_cps
            e p
            (fun v
             => match v with
                | Some v => match f v with
                            | Some fv => fv
                            | None => default tt
                            end
                | None => default tt
                end)
     end.

Inductive decision_tree :=
| Leaf (k : nat)
| Failure
| Switch (ccases : forall n, ctor n -> decision_tree) (lit_case : decision_tree)
| Swap (i : nat) (cont : decision_tree).

Definition swap_list {A} (i j : nat) (ls : list A) : option (list A)
  := match nth_error ls i, nth_error ls j with
     | Some vi, Some vj => Some (set_nth i vj (set_nth j vi ls))
     | _, _ => None
     end.

Fixpoint break_list_cps {T A} (ls : list A) (n : nat) (cont : option (list A) -> option (list A) -> T) {struct n} : T
  := match n, ls with
     | Datatypes.O, _ => cont (Some nil) (Some ls)
     | Datatypes.S n', x :: xs
       => @break_list_cps
            T A xs n'
            (fun first rest => cont (option_map (cons x) first) rest)
     | Datatypes.S _, nil
       => cont None None
     end.

Definition eta_ctor_cps {T n} (c : ctor n) (f : forall n, ctor n -> T) : T
  := match c with
     | O => f _ O
     | S => f _ S
     | Add => f _ Add
     end.


Fixpoint eval_decision_tree {T} (ctx : list expr) (d : decision_tree) (cont : option nat -> list expr -> T) {struct d} : T
  := match d with
     | Leaf k => cont (Some k) ctx
     | Failure => cont None ctx
     | Switch ccases lit_case
       => match ctx with
          | AppCtor _ c args :: ctx'
            => eta_ctor_cps
                 c
                 (fun n c
                  => break_list_cps
                       args n
                       (fun args' should_be_nil
                        => match args', should_be_nil with
                           | Some args', Some nil
                             => @eval_decision_tree
                                  T (args' ++ ctx') (ccases _ c)
                                  (fun k ctx''
                                   => break_list_cps
                                        ctx'' (arg_count c)
                                        (fun args'' ctx'''
                                         => match args'', ctx''' with
                                            | Some args'', Some ctx'''
                                              => cont k (AppCtor c args'' :: ctx''')
                                            | _, _ => cont None ctx
                                            end))
                           | _, _ => cont None ctx
                           end))
          | Literal n :: ctx'
            => @eval_decision_tree
                 T ctx' lit_case
                 (fun k ctx''
                  => cont k (Literal n :: ctx''))
          | nil => cont None ctx
          end
     | Swap i d'
       => match swap_list 0 i ctx with
          | Some ctx'
            => @eval_decision_tree
                 T ctx' d'
                 (fun k ctx''
                  => match swap_list 0 i ctx'' with
                     | Some ctx''' => cont k ctx'''
                     | None => cont None ctx
                     end)
          | None => cont None ctx
          end
     end.

Definition eval_rewrite_rules
           (d : decision_tree)
           (rew : list { p : pattern & binding_dataT p -> option expr })
           (e : expr)
  : expr
  := eval_decision_tree
       (e::nil) d
       (fun k ctx
        => match k, ctx with
           | Some k', e'::nil
             => match nth_error rew k' with
                | Some (existT p f)
                  => bind_data_cps
                       e' p
                       (fun v
                        => match v with
                           | Some v => match f v with
                                       | Some fv => fv
                                       | None => e
                                       end
                           | None => e
                           end)
                | None => e
                end
           | _, _ => e
           end).

Local Notation enumerate ls
  := (List.combine (List.seq 0 (List.length ls)) ls).

Fixpoint first_satisfying_helper {A B} (f : A -> option B) (ls : list A) : option B
  := match ls with
     | nil => None
     | cons x xs
       => match f x with
          | Some v => Some v
          | None => first_satisfying_helper f xs
          end
     end.

Definition get_index_of_first_non_wildcard (p : list pattern) : option nat
  := first_satisfying_helper
       (fun '(n, x) => match x with
                       | Wildcard => None
                       | _ => Some n
                       end)
       (enumerate p).

Definition refine_pattern_literal (p : nat * list pattern) : option (nat * list pattern)
  := match p with
     | (n, Wildcard::ps)
     | (n, pLiteral::ps)
       => Some (n, ps)
     | (_, pCtor _ _ _::_)
     | (_, nil)
       => None
     end.
Definition refine_pattern_ctor {n} (c : ctor n) (p : nat * list pattern) : option (nat * list pattern)
  := match p with
     | (k, Wildcard::ps)
       => Some (k, List.repeat Wildcard n ++ ps)
     | (k, pCtor _ c' args::ps)
       => ctor_beq_cps
            c c'
            (fun b
             => if b
                then Some (k, args ++ ps)
                else None)
     | (_, pLiteral::_)
     | (_, nil)
       => None
     end.

Fixpoint omap {A B} (f : A -> option B) (ls : list A) : list B
  := match ls with
     | nil => nil
     | x :: xs => match f x with
                  | Some fx => fx :: omap f xs
                  | None => omap f xs
                  end
     end.

Definition compile_rewrites_step
           (compile_rewrites : list (nat * list pattern) -> option decision_tree)
           (pattern_matrix : list (nat * list pattern))
  : option decision_tree
  := match pattern_matrix with
     | nil => Some Failure
     | (n1, p1) :: ps
       => match get_index_of_first_non_wildcard p1 with
          | None (* p1 is all wildcards *)
            => Some (Leaf n1)
          | Some Datatypes.O
            => lit_case <- compile_rewrites (omap refine_pattern_literal pattern_matrix);
                 O_case <- compile_rewrites (omap (refine_pattern_ctor O) pattern_matrix);
                 S_case <- compile_rewrites (omap (refine_pattern_ctor S) pattern_matrix);
                 Add_case <- compile_rewrites (omap (refine_pattern_ctor Add) pattern_matrix);
                 Some (Switch
                         (fun _ c
                          => match c with
                             | O => O_case
                             | S => S_case
                             | Add => Add_case
                             end)
                         lit_case)
          | Some i
            => let pattern_matrix'
                   := List.map
                        (fun '(n, ps)
                         => (n,
                             match swap_list 0 i ps with
                             | Some ps' => ps'
                             | None => nil (* should be impossible *)
                             end))
                        pattern_matrix in
               d <- compile_rewrites pattern_matrix';
                 Some (Swap i d)
          end
     end%option.

Fixpoint compile_rewrites' (fuel : nat) (pattern_matrix : list (nat * list pattern))
  : option decision_tree
  := match fuel with
     | Datatypes.O => None
     | Datatypes.S fuel' => compile_rewrites_step (@compile_rewrites' fuel') pattern_matrix
     end.

Definition compile_rewrites (fuel : nat) (ps : list { p : pattern & binding_dataT p -> option expr })
  := compile_rewrites' fuel (enumerate (List.map (fun p => projT1 p :: nil) ps)).

Notation make_rewrite p f := (existT (fun p' : pattern => binding_dataT p' -> option expr) p%pattern f%expr).

Definition rewrite_rules : list { p : pattern & binding_dataT p -> option expr }
  := [make_rewrite (0 + ??) (fun '(_, (x, tt)) => Some x);
        make_rewrite (?? + 0) (fun '(x, _) => Some x);
        make_rewrite (#? + #?) (fun '(x, (y, tt)) => Some (#(x + y)));
        make_rewrite (??.+1 + ??) (fun '((x, tt), (y, tt)) => Some ((x+y).+1));
        make_rewrite (?? + ??.+1) (fun '(x, ((y, tt), tt)) => Some ((x+y).+1))]%list.

Definition dtree : decision_tree
  := Eval compute in invert_Some (compile_rewrites 10 rewrite_rules).
(*
Fixpoint dorewrite' (e : expr) : expr
  := match e with
     | AppCtor Add (x::y::nil)
       => dlet x' := dorewrite' x in
          dlet y' := dorewrite' y in
          domatch rewrite_rules (AppCtor Add (x' :: y' :: nil))
     | AppCtor c args
       => dlet args' := List.map dorewrite' args in
          AppCtor c args'
     | Literal n => Literal n
     end.

Arguments bind_data_cps / .
Arguments dorewrite' / .
Arguments rewrite_rules / .
Arguments domatch / .
Definition dorewrite
  := Eval cbn [bind_data_cps dorewrite' rewrite_rules domatch ctor_beq ctor_beq_cps list_rect Option.bind] in dorewrite'.
 *)
Definition dorewrite1 (e : expr) : expr
  := eval_rewrite_rules dtree rewrite_rules e.
Fixpoint dorewrite' (e : expr) : expr
  := match e with
     | AppCtor _ Add (x::y::nil)
       => dlet x' := dorewrite' x in
          dlet y' := dorewrite' y in
          dorewrite1 (AppCtor Add (x' :: y' :: nil))
     | AppCtor _ c args
       => dlet args' := List.map dorewrite' args in
          AppCtor c args'
     | Literal n => Literal n
     end.
Arguments bind_data_cps / .
Arguments dorewrite1 / .
Arguments dorewrite' / .
Arguments rewrite_rules / .
Arguments domatch / .
Arguments eval_rewrite_rules / .
Arguments dtree / .
Arguments eval_decision_tree / .
Arguments arg_count / .
Arguments eta_ctor_cps / .
Arguments break_list_cps / .
Arguments option_map _ _ _ !_ / .
Arguments swap_list _ !_ !_ !_ / .
Arguments set_nth _ !_ _ !_ / .
Definition dorewrite
  := Eval cbn [dorewrite' dorewrite1 eval_rewrite_rules dtree eval_decision_tree arg_count eta_ctor_cps break_list_cps option_map List.app rewrite_rules nth_error bind_data_cps ctor_beq_cps list_rect Option.bind swap_list set_nth update_nth] in dorewrite'.
Print dorewrite.

Module Notations.
  Inductive rawpattern :=
  | Any
  | AnyLiteral
  | rpCtor (c : ctor) (args : list rawpattern).

  Fixpoint bind_rawpattern (p : rawpattern) (T : Type)
    := match p with
       | Any => expr -> T
       | AnyLiteral => nat -> T
       | rpCtor _ args
         => fold_right
              (fun p T => bind_rawpattern p T)
              T
              args
       end.

  Notation "x 'when' y" := (if y then Some x else None) (at level 70).

  Fixpoint compile' {T} (p : rawpattern)
    : forall (rew : bind_rawpattern p T),
      { p : pattern & binding_dataT p -> option T }.
    refine match p return bind_rawpattern p _ -> _ with
           | Any
             => fun rew
                => existT (fun p => binding_dataT p -> option T)
                          Wildcard
                          (fun v => Some (rew v))
           | AnyLiteral
             => fun rew
                => existT (fun p => binding_dataT p -> option T)
                          Wildcard
                          (fun e => match e with
                                    | Literal v => Some (rew v)
                                    | _ => None
                                    end)
           | rpCtor c args
             => fun rew
                => let '(existT ps rew')
                       := (list_rect
                             (fun args
                              => fold_right bind_rawpattern T args
                                 -> { p : list pattern & hlist binding_dataT p -> option T })
                             (fun v
                              => existT (fun p => hlist binding_dataT p -> option T)
                                        nil
                                        (fun _ => Some v))
                             (fun rp _ rec
                              => _)
                             args
                             rew) in
                   existT (fun p => binding_dataT p -> option T)
                          (pCtor c ps)
                          rew'
           end.
    cbn in *.
    Focus 3.
    cbn in *.

            cbn.


  Delimit Scope pattern_scope with pattern.
  Bind Scope pattern_scope with rawpattern.
  Notation "0" := (AppCtor O nil) : pattern_scope.
  Notation "n '.+1'" := (AppCtor S (n :: nil)) (at level 10, format "n '.+1'") : pattern_scope.
  Notation "x + y" := (AppCtor Add (x :: y :: nil)) : pattern_scope.
  Notation "# n" := (Literal n) : pattern_scope.



Fixpoint is_instance_of (e : expr) (p : pattern) : bool
  := match p, e with
     | Wildcard, _ => true
     | pCtor c args, AppCtor c' args'
       => (ctor_beq c c')
            && (Nat.eqb (List.length args) (List.length args'))
            && (fold_right
                  andb
                  true
                  (map2 is_instance_of args' args))
     end%bool.


Fixpoint not_instance_of (e : expr) (p : pattern) : bool
  := match p, e with
     | Wildcard, _ => false
     | pCtor c args, AppCtor c' args'
       => (negb (ctor_beq c c'))
            || (negb (Nat.eqb (List.length args) (List.length args')))
            || (fold_right
                  orb
                  false
                  (map2 not_instance_of args' args))
     end%bool.




Module type.
  Inductive type := Z | arrow (s d : type).

  Fixpoint for_each_lhs_of_arrow (f : type -> Type) (t : type) : Type
    := match t with
       | Z => unit
       | arrow s d => f s * @for_each_lhs_of_arrow f d
       end.

  Fixpoint final_codomain (t : type) : type
    := match t with
       | Z as t => t
       | arrow s d => @final_codomain d
       end.

  Fixpoint interp (t : type) : Type
    := match t with
       | Z => BinInt.Z
       | arrow s d => interp s -> interp d
       end.

  Fixpoint try_transport (P : type -> Type) (t1 t2 : type) : P t1 -> option (P t2)
    := match t1, t2 return P t1 -> option (P t2) with
       | Z, Z => fun v => Some v
       | arrow s d, arrow s' d'
         => fun v
            => (v' <- try_transport (fun s => P (arrow s d)) s s' v;
                  try_transport (fun d => P (arrow s' d)) d d' v')
       | Z, _
       | arrow _ _, _
         => fun _ => None
       end%option.
End type.
Notation type := type.type.
Delimit Scope etype_scope with etype.
Bind Scope etype_scope with type.type.
Infix "->" := type.arrow : etype_scope.

Module expr.
  Section with_var.
    Context {ident : type -> Type}
            {var : type -> Type}.

    Inductive expr : type -> Type :=
    | Ident {t} (idc : ident t) : expr t
    | Var {t} (v : var t) : expr t
    | Abs {s d} (f : var s -> expr d) : expr (s -> d)
    | App {s d} (f : expr (s -> d)) (x : expr s) : expr d
    | LetIn {A B} (x : expr A) (f : var A -> expr B) : expr B
    .
  End with_var.

  Module Export Notations.
    Delimit Scope expr_scope with expr.
    Bind Scope expr_scope with expr.
    Infix "@" := App : expr_scope.
    Notation "\ x .. y , f" := (Abs (fun x => .. (Abs (fun y => f%expr)) .. )) : expr_scope.
    Notation "'λ' x .. y , f" := (Abs (fun x => .. (Abs (fun y => f%expr)) .. )) : expr_scope.
    Notation "'expr_let' x := A 'in' b" := (LetIn A (fun x => b%expr)) : expr_scope.
    Notation "'$' x" := (Var x) (at level 10, format "'$' x") : expr_scope.
    Notation "### x" := (Ident x) : expr_scope.
  End Notations.
End expr.
Import expr.Notations.
Notation expr := expr.expr.

Module ident.
  Section with_base.
    Inductive ident : type -> Type :=
    | Literal (v : Z) : ident type.Z
    | Add : ident (type.Z -> type.Z -> type.Z)
    | Sub : ident (type.Z -> type.Z -> type.Z)
    | Opp : ident (type.Z -> type.Z)
    .
  End with_base.

  Module Export Notations.
    Delimit Scope ident_scope with ident.
    Bind Scope ident_scope with ident.
    Global Arguments expr.Ident {ident%function var%function t%etype} idc%ident.
    Notation "## x" := (Literal x) : ident_scope.
    Notation "## x" := (expr.Ident (Literal x)) : expr_scope.
    Notation "# x" := (expr.Ident x) : expr_scope.
    Notation "x + y" := (#Add @ x @ y)%expr : expr_scope.
    Notation "x - y" := (#Sub @ x @ y)%expr : expr_scope.
    Notation "- x" := (#Opp @ x)%expr : expr_scope.
  End Notations.
End ident.
Import ident.Notations.
Notation ident := ident.ident.

Section invert.
  Section with_var.
    Context {ident : type -> Type}
            {var : type -> Type}.

    Definition invert_Ident {t} (e : @expr ident var t) : option (ident t)
      := match e with
         | expr.Ident t idc => Some idc
         | _ => None
         end.
  End with_var.
End invert.

Module Rewrite.
  Module Rule.
    Section with_var.
      Context {ident : type -> Type}
              {var : type -> Type}
              (invert_Literal : forall t, ident t -> option (type.interp t))
              (ident_beq : forall t, ident t -> ident t -> bool).
      Local Notation expr := (@expr ident).
      Local Notation context := (list { t : _ & @expr var t }).

      Inductive pattern : type -> Type :=
      | Ident {t} (idc : ident t) : pattern t
      | Any t : pattern t
      | AnyLiteral t : pattern t
      | App {s d} (f : pattern (s -> d)) (x : pattern s) : pattern d.

      Inductive switch_kind :=
      | SIdent {t} (idc : ident t)
      | SApp.

      Inductive decision_tree :=
      | Leaf (k : nat)
      | Failure
      | Switch
          (app_case : decision_tree)
          (literal_case : decision_tree)
          (ident_cases : list ({ t : _ & ident t } * decision_tree))
          (default : decision_tree)
      | Swap (i : nat) (t : decision_tree).

      Fixpoint eval_decision_tree
               {T}
               (tree : decision_tree)
               (v : context)
               (cont : context * nat -> T)
               {struct tree}
        : option T.
        refine match tree with
               | Leaf k => Some (cont (v, k))
               | Failure => None
               | Switch app_case literal_case ident_cases default
                 => match v with
                    | (existT t0 v0) :: vs
                      => let default _
                             := @eval_decision_tree
                                  T default v
                                  (fun '(vs', k) => cont (existT _ t0 v0 :: vs', k)) in
                         match
                    | nil => None
                    end
               | Swap i rest
                 => (v0 <- nth_error v 0;
                     vi <- nth_error v i;
                     @eval_decision_tree
                       T rest
                       (set_nth 0 vi (set_nth i v0 v))
                       cont)
               end%option.
            := refine
               (ls : list { p : pattern t & structuredT p (@expr var t) })


      Inductive matchdata : type -> Type :=
      | mIdent {t} (idc : ident t) : matchdata t
      | mAny {t} (idx : nat) : matchdata t
      | mAnyLiteral {t} (idx : nat) : matchdata t
      | mApp {s d} (f : matchdata (s -> d)) (x : matchdata s) : matchdata d.

      Fixpoint structuredT {t} (p : pattern t) (codomain : Type) : Type
        := match p with
           | Ident t idc => codomain
           | Any t => @expr var t -> codomain
           | AnyLiteral t => type.interp t -> codomain
           | App s d f x => @structuredT _ f (@structuredT _ x codomain)
           end.

      Fixpoint app_structured {t t' T} (p : pattern t) (data : matchdata t') (ctx : context) : structuredT p T -> option T.
        refine match p, data return structuredT p T -> option T with
           | Ident t idc, mIdent t' idc'
             => fun v
                => (idc'' <- type.try_transport _ _ _ idc';
                      if ident_beq _ idc idc''
                      then Some v
                      else None)
           | Any t, mAny t' idx
             => fun f
                => (e <- nth_error ctx (List.length ctx - idx);
                    e' <- type.try_transport _ _ _ (projT2 e);
                    e'' <- type.try_transport _ t' t e';
                    Some (f e''))
           | AnyLiteral
           | _, _ => _ end%option.
        Focus 5.
        cbn in *.
           | Any t idx
             => fun f
                => (e <- nth_error ctx (List.length ctx - idx);
                      e' <- type.try_transport _ _ _ (projT2 e);
                      Some (f e'))
           | AnyLiteral t idx
             => fun f
                => (e <- nth_error ctx (List.length ctx - idx);
                      e' <- type.try_transport _ _ _ (projT2 e);
                      idc <- invert_Ident e';
                      v <- invert_Literal _ idc;
                      Some (f v))
           | App s d f x
             => fun F
                => (F' <- @app_structured _ (structuredT x T) f ctx F;
                      @app_structured _ _ x ctx F')
           end%option.

      Definition side_conditionT {t} (p : pattern t) := structuredT p bool.

      Inductive stepdiscriminate_result (t : type) :=
      | stepped
          (new_structure : pattern t)
          (ctx : context)
      | matched
      | failed_to_match.

      Fixpoint stepdiscriminate {t}
               (cur_structure : pattern t)
               (ctx : context)
               (p : pattern t) (s : side_conditionT p) (rew : structuredT p (@expr var t))
               {struct cur_structure}
        : stepdiscriminate_result t.
        refine (match cur_structure in pattern t
                      return (forall (p : pattern t) (s : side_conditionT p) (rew : structuredT p (@expr var t)),
                                 stepdiscriminate_result t)
                with
                | Ident t idc
                  => _
                | Any t idx => _
                | AnyLiteral t idx => _
                | App s d f x => _
                end p s rew).
        cbn.


      Fixpoint domatch {t} (p : pattern t)
        : forall (rest : list { p : pattern t & structuredT p (@expr var t) })
                 (rew : structuredT p (@expr var t))
                 (e : @expr var t),
          @expr var t.
        refine match p in pattern t
                     return  (forall (rest : list { p : pattern t & structuredT p (@expr var t) })
                                     (rew : structuredT p (@expr var t))
                                     (e : @expr var t),
                                 @expr var t) with
             | Ident t idc => _
             | Any t idx => _
             | AnyLiteral t idx => _
             | App s d f x => _
             end.


      Fixpoint domatchlist {t} (ls : list { p : pattern t & structuredT p (@expr var t) })
        : @expr var t
      with domatch {t} (p : pattern t)
           : forall (rest : list { p : pattern t & structuredT p (@expr var t) })
                    (rew : structuredT p (@expr var t))
                    (e : @expr var t),
          @expr var t.



    End with_var.
  End Rule.

  Module Replacement.
    Section with_var.
      Context {base_type : Type}.
      Local Notation type := (type base_type).
      Context {ident : type -> Type}
              {var : type -> Type}
              (base_interp : base_type -> Type).

      Inductive pattern : type -> Type :=
      | Ident {t} (idc : ident t) : pattern t
      | Any {t} (idx : nat) : pattern t
      | AnyLiteral {t} (idx : nat) : pattern t
      | App {s d} (f : pattern (s -> d)) (x : pattern s) : pattern d.
    End with_var.
  End Rule.
      Inductive structured : type -> Type :=
      | Ident {t} (idc : ident t) : pattern t
      | Any {t} (idx : nat) : pattern t
      | AnyLiteral {t} (idx : nat) : pattern t
      | App {s d} (f : pattern (s -> d)) (x : pattern s) : pattern d.

      Section compile.
        Fixpoint compile {t}
    End with_var.
  End Rule.
