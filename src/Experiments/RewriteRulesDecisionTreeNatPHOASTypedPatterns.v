Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.LetIn.
Import ListNotations.

Set Boolean Equality Schemes.
Inductive type := Nat | Arrow (s d : type).
Bind Scope ctype_scope with type.
Delimit Scope ctype_scope with ctype.
Infix "->" := Arrow : ctype_scope.

Module type.
  Fixpoint interp (t : type) : Set
    := match t with
       | Nat => nat
       | Arrow s d => interp s -> interp d
       end.
  Fixpoint try_transport_cps {T} (P : type -> Type) (t1 t2 : type) : P t1 -> (option (P t2) -> T) -> T
    := match t1, t2 with
       | Nat, Nat => fun v k => k (Some v)
       | Arrow s d, Arrow s' d'
         => fun v k
            => try_transport_cps
                 (fun s => P (Arrow s _)) _ _ v
                 (fun v'
                  => match v' with
                     | Some v'
                       => try_transport_cps
                            (fun d => P (Arrow _ d)) _ _ v'
                            k
                     | None => k None
                     end)
       | Nat, _
       | Arrow _ _, _
         => fun _ k => k None
       end.
End type.

Inductive ident : type -> Set :=
| O : ident Nat
| S : ident (Nat -> Nat)
| Add : ident (Nat -> Nat -> Nat).

Fixpoint ident_beq_cps {T t t'} (X : ident t) (Y : ident t') (k : bool -> T) {struct X} : T
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

Definition eta_option_ident_cps {T} (f : forall t, ident t -> option (T t))
  : option (forall t, ident t -> T t)
  := (fO <- f _ O;
        fS <- f _ S;
        fAdd <- f _ Add;
        Some (fun _ c
              => match c with
                 | O => fO
                 | S => fS
                 | Add => fAdd
                 end))%option.

Definition eta_ident_cps {T t} (c : ident t) (f : forall t, ident t -> T t) : T t
  := Eval cbv [invert_Some Option.bind eta_option_ident_cps] in
      invert_Some (eta_option_ident_cps (fun _ c' => Some (f _ c'))) _ c.

Inductive expr : type -> Set :=
| Ident {t} (idc : ident t) : expr t
| App {s d} (f : expr (s -> d)) (x : expr s) : expr d
| Literal (n : nat) : expr Nat.

Inductive pattern : type -> Set :=
| Wildcard {t} : pattern t
| pIdent {t} (idc : ident t) : pattern t
| pApp {s d} (f : pattern (s -> d)) (x : pattern s) : pattern d
| pLiteral : pattern Nat.

Delimit Scope expr_scope with expr.
Bind Scope expr_scope with expr.
Notation "# idc" := (Ident idc) : expr_scope.
Notation "## n" := (Literal n) : expr_scope.
Infix "@" := App : expr_scope.
Notation "0" := (#O)%expr : expr_scope.
Notation "n '.+1'" := (#S @ n)%expr (at level 10, format "n '.+1'") : expr_scope.
Notation "x + y" := (#Add @ x @ y)%expr : expr_scope.

Delimit Scope pattern_scope with pattern.
Bind Scope pattern_scope with pattern.
Notation "# idc" := (pIdent idc) : pattern_scope.
Notation "#?" := pLiteral : pattern_scope.
Notation "??" := Wildcard : pattern_scope.
Infix "@" := pApp : pattern_scope.
Notation "0" := (#O)%pattern : pattern_scope.
Notation "n '.+1'" := (#S @ n)%pattern (at level 10, format "n '.+1'") : pattern_scope.
Notation "x + y" := (#Add @ x @ y)%pattern : pattern_scope.

Record > anyexpr := wrap { anyexpr_ty : type ; unwrap :> expr anyexpr_ty }.
Arguments wrap {_} _.

Record > anypattern := pwrap { anypattern_ty : type ; punwrap :> pattern anypattern_ty }.
Arguments pwrap {_} _.

Definition hlist {A} (f : A -> Set) (ls : list A)
  := fold_right
       (fun a b : Set => prod a b)
       unit
       (map f ls).

Fixpoint binding_dataT {t} (p : pattern t)
  := match p with
     | Wildcard t => expr t
     | pLiteral => nat
     | pApp _ _ f x => binding_dataT f * binding_dataT x
     | pIdent _ _ => unit
     end%type.

Fixpoint bind_data_cps {T t t'} (e : expr t) (p : pattern t') {struct p}
  : (option (binding_dataT p) -> T) -> T
  := match p return (option (binding_dataT p) -> T) -> T with
     | Wildcard _
       => fun k => type.try_transport_cps _ _ _ e k
     | pLiteral
       => fun k
          => match e with
             | Literal n => k (Some n)
             | _ => k None
             end
     | pApp _ _ pf px
       => fun k
          => match e with
             | App _ _ f x
               => @bind_data_cps
                    _ _ _ f pf
                    (fun f'
                     => match f' with
                        | None => k None
                        | Some f''
                          => @bind_data_cps
                               _ _ _ x px
                               (fun x'
                                => k (x'' <- x';
                                        Some (f'', x'')))
                        end)
             | _ => k None
             end
     | pIdent _ pidc
       => fun k
          => match e with
             | Ident _ idc
               => ident_beq_cps
                    pidc idc
                    (fun b
                     => if b
                        then k (Some tt)
                        else k None)
             | _ => k None
             end
     end%option.

Fixpoint domatch {t} (ps : list { t' : type & { p : pattern t' & binding_dataT p -> option (expr t') } })
         (e : expr t)
  : expr t
  := match ps with
     | nil => e
     | existT _ (existT p f) :: ps
       => let default _ := domatch ps e in
          bind_data_cps
            e p
            (fun v
             => match option_map f v with
                | Some (Some fv)
                  => type.try_transport_cps
                       _ _ _ fv
                       (fun fv => match fv with
                                  | Some fv => fv
                                  | None => default tt
                                  end)
                | _ => default tt
                end)
     end.

Inductive decision_tree :=
| TryLeaf (k : nat) (onfailure : decision_tree)
| Failure
| Switch (app_case : decision_tree)
         (icases : forall t, ident t -> decision_tree)
         (lit_case : decision_tree)
| Swap (i : nat) (cont : decision_tree).

Definition swap_list {A} (i j : nat) (ls : list A) : option (list A)
  := match nth_error ls i, nth_error ls j with
     | Some vi, Some vj => Some (set_nth i vj (set_nth j vi ls))
     | _, _ => None
     end.

Fixpoint eval_decision_tree {T} (ctx : list anyexpr) (d : decision_tree) (cont : option nat -> list anyexpr -> option (unit -> T) -> T) {struct d} : T
  := match d with
     | TryLeaf k onfailure
       => cont (Some k) ctx
               (Some (fun 'tt => @eval_decision_tree T ctx onfailure cont))
     | Failure => cont None ctx None
     | Switch app_case icases lit_case
       => match ctx with
          | nil => cont None ctx None
          | Literal n :: ctx'
            => @eval_decision_tree
                 T ctx' lit_case
                 (fun k ctx''
                  => cont k (wrap (Literal n) :: ctx''))
          | App s d f x :: ctx'
            => @eval_decision_tree
                 T (wrap f :: wrap x :: ctx') app_case
                 (fun k ctx''
                  => match ctx'' with
                     | wrap tf f' :: wrap tx x' :: ctx'''
                       => type.try_transport_cps
                            _ _ (s -> d) f'
                            (fun f'
                             => type.try_transport_cps
                                  _ _ s x'
                                  (fun x'
                                   => match f', x' with
                                      | Some f'', Some x''
                                        => cont k (wrap (App f'' x'') :: ctx''')
                                      | _, _ => cont None ctx
                                      end))
                     | _ => cont None ctx
                     end)
          | Ident t idc :: ctx'
            => eta_ident_cps
                 idc
                 (fun _ idc'
                  => @eval_decision_tree
                       T ctx' (icases _ idc')
                       (fun k ctx''
                        => cont k (wrap (Ident idc') :: ctx'')))
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
           {t}
           (d : decision_tree)
           (rew : list { t' : type & { p : pattern t' & binding_dataT p -> option (expr t') } })
           (e : expr t)
  : expr t
  := eval_decision_tree
       (wrap e::nil) d
       (fun k ctx default_on_rewrite_failure
        => match k, ctx with
           | Some k', e'::nil
             => match nth_error rew k' with
                | Some (existT _ (existT p f))
                  => bind_data_cps
                       e' p
                       (fun v
                        => match option_map f v with
                           | Some (Some fv)
                             => type.try_transport_cps
                                  _ _ _ fv
                                  (fun fv => match fv, default_on_rewrite_failure with
                                             | Some fv, _ => fv
                                             | None, Some default => default tt
                                             | None, None => e
                                             end)
                           | _ => e
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

Definition get_index_of_first_non_wildcard (p : list anypattern) : option nat
  := first_satisfying_helper
       (fun '(n, pwrap _ x) => match x with
                       | Wildcard _ => None
                       | _ => Some n
                       end)
       (enumerate p).

Definition refine_pattern_literal (p : nat * list anypattern) : option (nat * list anypattern)
  := match p with
     | (n, Wildcard Nat::ps)
     | (n, pLiteral::ps)
       => Some (n, ps)
     | (_, Wildcard _::_)
     | (_, pApp _ _ _ _::_)
     | (_, pIdent _ _::_)
     | (_, nil)
       => None
     end.
Definition refine_pattern_app (s d : type) (p : nat * list anypattern)
  : option (nat * list anypattern)
  := match p with
     | (n, Wildcard t::ps)
       => if type_beq d t
          then Some (n, pwrap (@Wildcard s) :: pwrap (@Wildcard d) :: ps)
          else None
     | (n, pApp s' d' f x::ps)
       => if (type_beq s s' && type_beq d d')%bool
          then Some (n, pwrap f :: pwrap x :: ps)
          else None
     | (_, pLiteral::_)
     | (_, pIdent _ _::_)
     | (_, nil)
       => None
     end.
Definition refine_pattern_pident {t} (c : ident t) (p : nat * list anypattern) : option (nat * list anypattern)
  := match p with
     | (k, Wildcard t'::ps)
       => if type_beq t t'
          then Some (k, ps)
          else None
     | (k, pIdent _ c'::ps)
       => ident_beq_cps
            c c'
            (fun b
             => if b
                then Some (k, ps)
                else None)
     | (_, pApp _ _ _ _::_)
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
           (compile_rewrites : list (nat * list anypattern) -> option decision_tree)
           (pattern_matrix : list (nat * list anypattern))
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
                 app_case <- compile_rewrites (omap refine_pattern_app pattern_matrix);
                 icases
                   <- (eta_option_ident_cps
                         (fun c => compile_rewrites (omap (refine_pattern_pident c) pattern_matrix)));
                 Some (Switch app_case icases lit_case)
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

Definition compile_rewrites (fuel : nat) (ps : list { p : pattern & { t' : type & binding_dataT p -> option (expr t') } })
  := compile_rewrites' fuel (enumerate (List.map (fun p => projT1 p :: nil) ps)).

Fixpoint with_bindingsT (p : pattern) (T : Type)
  := match p with
     | Wildcard None => forall t, expr t -> T
     | Wildcard (Some t) => expr t -> T
     | pLiteral => nat -> T
     | pApp f x => with_bindingsT f (with_bindingsT x T)
     | pIdent _ => T
     end.

Fixpoint lift_with_bindings {p A B} (F : A -> B) {struct p} : with_bindingsT p A -> with_bindingsT p B
  := match p return with_bindingsT p A -> with_bindingsT p B with
     | Wildcard (Some _) => fun f e => F (f e)
     | Wildcard None => fun f t e => F (f t e)
     | pLiteral => fun f e => F (f e)
     | pApp f x
       => @lift_with_bindings f _ _ (@lift_with_bindings x _ _ F)
     | pIdent _ => F
     end.

Fixpoint app_binding_data {T p} : forall (f : with_bindingsT p T) (v : binding_dataT p), T
  := match p return forall (f : with_bindingsT p T) (v : binding_dataT p), T with
     | Wildcard None
       => fun f v => f _ (unwrap v)
     | Wildcard (Some _)
     | pLiteral
       => fun f => f
     | pApp f x
       => fun F '(fv, xv)
          => @app_binding_data _ x (@app_binding_data _ f F fv) xv
     | pIdent _
       => fun v 'tt => v
     end.

Notation make_rewrite' p f
 := (existT
       (fun p' : pattern => { t' : type & binding_dataT p' -> option (expr t') })
       p%pattern
       (existT
          (fun t' : type => binding_dataT p -> option (expr t'))
          _
          (@app_binding_data _ p%pattern f%expr))).
Notation make_rewrite p f
  := (let f' := (@lift_with_bindings p _ _ (fun x => Some x) f%expr) in
      make_rewrite' p f').

Definition rewrite_rules : list { p : pattern & { t' : type & binding_dataT p -> option (expr t') } }
  := [make_rewrite (0 + ??ℕ) (fun x => x);
        make_rewrite (??ℕ + 0) (fun x => x);
        make_rewrite (#? + #?) (fun x y => ##(x + y));
        make_rewrite (??ℕ.+1 + ??ℕ) (fun x y => (x+y).+1);
        make_rewrite (??ℕ + ??ℕ.+1) (fun x y => (x+y).+1)]%list.

Definition dtree : decision_tree
  := Eval compute in invert_Some (compile_rewrites 100 rewrite_rules).
Print dtree.
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
Definition dorewrite1 {t} (e : expr t) : expr t
  := eval_rewrite_rules dtree rewrite_rules e.

Fixpoint value (t : type)
  := match t with
     | Nat as t
       => expr t
     | Arrow s d => expr s -> value d
     end.

Fixpoint do_rewrite_ident {t} : expr t -> value t
  := match t return expr t -> value t with
     | Nat as t
       => fun e => dorewrite1 e
     | Arrow s d
       => fun f x => @do_rewrite_ident d (f @ x)%expr
     end.

Fixpoint dorewrite' {t} (e : expr t) : value t
  := match e in expr t return value t with
     | Ident t idc
       => eta_ident_cps idc (fun _ idc' => do_rewrite_ident #idc')
     | Literal _ as e => e
     | App Nat d f x => @dorewrite' _ f (@dorewrite' _ x)
     | App (Arrow _ _) d f x => @dorewrite' _ f x (* higher order, don't do anything with the argument *)
     end.

Arguments bind_data_cps / .
Arguments dorewrite1 / .
Arguments dorewrite' / .
Arguments rewrite_rules / .
Arguments domatch / .
Arguments eval_rewrite_rules / .
Arguments dtree / .
Arguments eval_decision_tree / .
Arguments eta_ident_cps / .
Arguments eta_ident_pident_cps / .
Arguments eta_option_ident_cps / .
Arguments eta_option_pident_cps / .
Arguments option_map _ _ _ !_ / .
Arguments swap_list _ !_ !_ !_ / .
Arguments set_nth _ !_ _ !_ / .
Arguments lift_with_bindings / .
Arguments app_binding_data / .
Arguments do_rewrite_ident / .
Arguments pident_of_ident / .
Arguments anyexpr_ty / .
Arguments unwrap / .
Definition dorewrite
  := Eval cbv [dorewrite' dorewrite1 do_rewrite_ident eval_rewrite_rules dtree eval_decision_tree eta_ident_cps eta_ident_pident_cps eta_option_ident_cps eta_option_pident_cps option_map List.app rewrite_rules nth_error bind_data_cps ident_beq_cps pident_beq_cps list_rect Option.bind swap_list set_nth update_nth lift_with_bindings app_binding_data pident_of_ident type.try_transport_cps unwrap anyexpr_ty] in @dorewrite'.
Arguments dorewrite {t} e.
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
