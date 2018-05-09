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

Definition eta_ctor_cps {T n} (c : ctor n) (f : forall n, ctor n -> T) : T
  := match c with
     | O => f _ O
     | S => f _ S
     | Add => f _ Add
     end.

Definition eta_option_ctor_cps {T} (f : forall n, ctor n -> option T)
  : option (forall n, ctor n -> T)
  := (fO <- f _ O;
        fS <- f _ S;
        fAdd <- f _ Add;
        Some (fun _ c
              => match c with
                 | O => fO
                 | S => fS
                 | Add => fAdd
                 end))%option.

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
| TryLeaf (k : nat) (onfailure : decision_tree)
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

Fixpoint eval_decision_tree {T} (ctx : list expr) (d : decision_tree) (cont : option nat -> list expr -> option (unit -> T) -> T) {struct d} : T
  := match d with
     | TryLeaf k onfailure
       => cont (Some k) ctx
               (Some (fun 'tt => @eval_decision_tree T ctx onfailure cont))
     | Failure => cont None ctx None
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
                           | _, _ => cont None ctx None
                           end))
          | Literal n :: ctx'
            => @eval_decision_tree
                 T ctx' lit_case
                 (fun k ctx''
                  => cont k (Literal n :: ctx''))
          | nil => cont None ctx None
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
          | None => cont None ctx None
          end
     end.

Definition eval_rewrite_rules
           (d : decision_tree)
           (rew : list { p : pattern & binding_dataT p -> option expr })
           (e : expr)
  : expr
  := eval_decision_tree
       (e::nil) d
       (fun k ctx default_on_rewrite_failure
        => match k, ctx with
           | Some k', e'::nil
             => match nth_error rew k' with
                | Some (existT p f)
                  => bind_data_cps
                       e' p
                       (fun v
                        => match v with
                           | Some v => match f v, default_on_rewrite_failure with
                                       | Some fv, _ => fv
                                       | None, Some default => default tt
                                       | None, None => e
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
            => (onfailure <- compile_rewrites ps;
                  Some (TryLeaf n1 onfailure))
          | Some Datatypes.O
            => lit_case <- compile_rewrites (omap refine_pattern_literal pattern_matrix);
                 ctor_case
                   <- (eta_option_ctor_cps
                         (fun _ c => compile_rewrites (omap (refine_pattern_ctor c) pattern_matrix)));
                 Some (Switch ctor_case lit_case)
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

Fixpoint with_bindingsT (p : pattern) (T : Type)
  := match p with
     | Wildcard => expr -> T
     | pLiteral => nat -> T
     | pCtor n c args
       => fold_right
            with_bindingsT
            T
            args
     end.

Fixpoint lift_with_bindings {p A B} (F : A -> B) {struct p} : with_bindingsT p A -> with_bindingsT p B
  := match p return with_bindingsT p A -> with_bindingsT p B with
     | Wildcard => fun f e => F (f e)
     | pLiteral => fun f e => F (f e)
     | pCtor n c args
       => list_rect
            (fun args => fold_right with_bindingsT A args -> fold_right with_bindingsT B args)
            F
            (fun x xs rec f
             => @lift_with_bindings
                  x _ _
                  rec
                  f)
            args
     end.

Fixpoint app_binding_data {T p} : forall (f : with_bindingsT p T) (v : binding_dataT p), T
  := match p return forall (f : with_bindingsT p T) (v : binding_dataT p), T with
     | Wildcard => fun f v => f v
     | pLiteral => fun f v => f v
     | pCtor n c args
       => list_rect
            (fun args => fold_right with_bindingsT T args -> hlist binding_dataT args -> T)
            (fun v 'tt => v)
            (fun x xs rec f '((v0, vs) : _ * hlist binding_dataT xs)
             => rec (@app_binding_data _ _ f v0) vs)
            args
     end.

Notation make_rewrite' p f := (existT (fun p' : pattern => binding_dataT p' -> option expr) p%pattern (@app_binding_data _ p%pattern f%expr)).
Notation make_rewrite p f
  := (let f' := (@lift_with_bindings p _ _ (fun x => Some x) f%expr) in
      make_rewrite' p f').

Definition rewrite_rules : list { p : pattern & binding_dataT p -> option expr }
  := [make_rewrite (0 + ??) (fun x => x);
        make_rewrite (?? + 0) (fun x => x);
        make_rewrite (#? + #?) (fun x y => #(x + y));
        make_rewrite (??.+1 + ??) (fun x y => (x+y).+1);
        make_rewrite (?? + ??.+1) (fun x y => (x+y).+1)]%list.

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
Arguments eta_option_ctor_cps / .
Arguments break_list_cps / .
Arguments option_map _ _ _ !_ / .
Arguments swap_list _ !_ !_ !_ / .
Arguments set_nth _ !_ _ !_ / .
Arguments lift_with_bindings / .
Arguments app_binding_data / .
Definition dorewrite
  := Eval cbn [dorewrite' dorewrite1 eval_rewrite_rules dtree eval_decision_tree arg_count eta_ctor_cps break_list_cps option_map List.app rewrite_rules nth_error bind_data_cps ctor_beq_cps list_rect Option.bind swap_list set_nth update_nth eta_option_ctor_cps lift_with_bindings app_binding_data] in dorewrite'.
Print dorewrite.
(* dorewrite =
fix dorewrite' (e : expr) : expr :=
  match e with
  | @AppCtor n (O as c) args | @AppCtor n (S as c) args =>
      dlet args' : list expr := map dorewrite' args in
      AppCtor c args'
  | @AppCtor n (Add as c) ([] as args) =>
      dlet args' : list expr := map dorewrite' args in
      AppCtor c args'
  | @AppCtor n (Add as c) ([x] as args) =>
      dlet args' : list expr := map dorewrite' args in
      AppCtor c args'
  | @AppCtor n (Add as c) [x; y] =>
      dlet x' : expr := dorewrite' x in
      dlet y' : expr := dorewrite' y in
      match x' with
      | 0%expr => y'
      | (x0.+1)%expr =>
          match y' with
          | 0%expr => (x0.+1)%expr
          | (x1.+1)%expr => ((x0 + x1.+1).+1)%expr
          | @AppCtor _ S (x1 :: _ :: _) | @AppCtor _ Add [x1] => (x' + y')%expr
          | (x1 + x2)%expr => ((x0 + (x1 + x2)).+1)%expr
          | @AppCtor _ Add (x1 :: x2 :: _ :: _) => (x' + y')%expr
          | #(n1)%expr => ((x0 + #(n1)).+1)%expr
          | _ => (x' + y')%expr
          end
      | @AppCtor _ S (x0 :: _ :: _) | @AppCtor _ Add [x0] => (x' + y')%expr
      | (x0 + x1)%expr =>
          match y' with
          | 0%expr => (x0 + x1)%expr
          | (x2.+1)%expr => ((x0 + x1 + x2).+1)%expr
          | @AppCtor _ S (x2 :: _ :: _) => (x' + y')%expr
          | _ => (x' + y')%expr
          end
      | @AppCtor _ Add (x0 :: x1 :: _ :: _) => (x' + y')%expr
      | #(n0)%expr =>
          match y' with
          | 0%expr => #(n0)%expr
          | (x0.+1)%expr => ((#(n0) + x0).+1)%expr
          | @AppCtor _ S (x0 :: _ :: _) => (x' + y')%expr
          | #(n1)%expr => #(n0 + n1)%expr
          | _ => (x' + y')%expr
          end
      | _ => (x' + y')%expr
      end
  | @AppCtor n (Add as c) ((x :: y :: _ :: _) as args) =>
      dlet args' : list expr := map dorewrite' args in
      AppCtor c args'
  | #(n)%expr => #(n)%expr
  end
     : expr -> expr

Argument scope is [expr_scope]
*)
