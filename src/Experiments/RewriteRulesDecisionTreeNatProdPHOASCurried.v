Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.LetIn.
Import ListNotations.

Set Boolean Equality Schemes.
Inductive base_type := Nat | Prod (A B : base_type).
Inductive type := Base (t : base_type) | Arrow (s : base_type) (d : type).
Coercion Base : base_type >-> type.
Bind Scope ctype_scope with type.
Bind Scope ctype_scope with base_type.
Delimit Scope ctype_scope with ctype.
Infix "->" := Arrow : ctype_scope.
Infix "*" := Prod : ctype_scope.

Inductive ident : type -> Set :=
| O : ident Nat
| S : ident (Nat -> Nat)
| Add : ident (Nat -> Nat -> Nat)
| Pair {A B : base_type} : ident (A -> B -> A * B)
| Fst {A B} : ident (A * B -> A)
| Snd {A B} : ident (A * B -> B).

Inductive pident : Set :=
| pO
| pS
| pAdd
| pPair
| pFst
| pSnd.

Inductive expr : type -> Set :=
| Ident {t} (idc : ident t) : expr t
| App {s d} (f : expr (s -> d)) (x : expr s) : expr d
| Literal (n : nat) : expr Nat.

Inductive pattern : Set :=
| Wildcard (t : option base_type)
| pIdent (idc : pident)
| pApp (f x : pattern)
| pLiteral.

Inductive rawexpr : Set :=
| rIdent {t} (idc : ident t) {t'} (alt : expr t')
| rApp (f x : rawexpr) {t} (alt : expr t)
| rLiteral (n : nat) {t} (alt : expr t)
| rExpr {t} (e : expr t).

Definition type_of_rawexpr (e : rawexpr) : type
  := match e with
     | rIdent t idc t' alt => t'
     | rApp f x t alt => t
     | rLiteral n t alt => t
     | rExpr t e => t
     end.
Definition expr_of_rawexpr (e : rawexpr) : expr (type_of_rawexpr e)
  := match e with
     | rIdent t idc t' alt => alt
     | rApp f x t alt => alt
     | rLiteral n t alt => alt
     | rExpr t e => e
     end.

Delimit Scope expr_scope with expr.
Bind Scope expr_scope with expr.
Notation "# idc" := (Ident idc) : expr_scope.
Notation "## n" := (Literal n) : expr_scope.
Infix "@" := App : expr_scope.
Notation "0" := (#O)%expr : expr_scope.
Notation "n '.+1'" := (#S @ n)%expr (at level 10, format "n '.+1'") : expr_scope.
Notation "x + y" := (#Add @ x @ y)%expr : expr_scope.
Notation "( x , y , .. , z )" := (#Pair @ .. (#Pair @ x @ y) .. @ z)%expr : expr_scope.

Delimit Scope pattern_scope with pattern.
Bind Scope pattern_scope with pattern.
Notation "#?" := pLiteral : pattern_scope.
Notation "??" := (Wildcard None) : pattern_scope.
Notation "??ℕ" := (Wildcard (Some Nat)) : pattern_scope.
Notation "??ℕℕ" := (Wildcard (Some (Prod Nat Nat))) : pattern_scope.
Notation "# idc" := (pIdent idc) : pattern_scope.
Infix "@" := pApp : pattern_scope.
Notation "0" := (#pO)%pattern : pattern_scope.
Notation "n '.+1'" := (#pS @ n)%pattern (at level 10, format "n '.+1'") : pattern_scope.
Notation "x + y" := (#pAdd @ x @ y)%pattern : pattern_scope.
Notation "( x , y , .. , z )" := (#pPair @ .. (#pPair @ x @ y) .. @ z)%pattern : pattern_scope.

Module type.
  Fixpoint try_transport_base_cps {T} (P : base_type -> Type) (t1 t2 : base_type)
           {struct t2}
  : P t1 -> (option (P t2) -> T) -> T
    := match t2 with
       | Nat
         => fun v k
            => match t1 with
               | Nat => fun v => k (Some v)
               | _ => fun _ => k None
               end v
       | Prod s d
         => fun v k
            => match t1 return P t1 -> _ with
               | Prod s' d'
                 => fun v
                    => try_transport_base_cps
                         (fun s => P (Prod s _)) _ _ v
                         (fun v'
                          => match v' with
                             | Some v'
                               => try_transport_base_cps
                                    (fun d => P (Prod _ d)) _ _ v'
                                    k
                             | None => k None
                             end)
               | _ => fun _ => k None
               end v
       end.

  Fixpoint try_transport_cps {T} (P : type -> Type) (t1 t2 : type) {struct t2} : P t1 -> (option (P t2) -> T) -> T
    := match t2 with
       | Base t2
         => fun v k
            => match t1 with
               | Base t1 => fun v => try_transport_base_cps P t1 t2 v k
               | _ => fun _ => k None
               end v
       | Arrow s d
         => fun v k
            => match t1 return P t1 -> _ with
               | Arrow s' d'
                 => fun v
                    => try_transport_base_cps
                         (fun s => P (Arrow s _)) _ _ v
                         (fun v'
                          => match v' with
                             | Some v'
                               => try_transport_cps
                                    (fun d => P (Arrow _ d)) _ _ v'
                                    k
                             | None => k None
                             end)
               | _ => fun _ => k None
               end v
       end.
End type.

Record > anyexpr := wrap { anyexpr_ty : type ; unwrap :> expr anyexpr_ty }.
Arguments wrap {_} _.

Definition pident_ident_beq {t} (X : pident) (Y : ident t) : bool
  := match X, Y with
     | pO, O
     | pS, S
     | pAdd, Add
     | pPair, Pair _ _
     | pFst, Fst _ _
     | pSnd, Snd _ _
       => true
     | pO, _
     | pS, _
     | pAdd, _
     | pPair, _
     | pFst, _
     | pSnd, _
       => false
     end.

Definition eta_ident_cps {T t} (idc : ident t)
           (f : forall t, ident t -> T t)
  : T t
  := match idc with
     | O => f _ O
     | S => f _ S
     | Add => f _ Add
     | Pair A B => f _ (@Pair A B)
     | Fst A B => f _ (@Fst A B)
     | Snd A B => f _ (@Snd A B)
     end.

Definition eta_option_pident_cps {T} (f : pident -> option T)
  : option (pident -> T)
  := (fO <- f pO;
        fS <- f pS;
        fAdd <- f pAdd;
        fPair <- f pPair;
        fFst <- f pFst;
        fSnd <- f pSnd;
        Some (fun c
              => match c with
                 | pO => fO
                 | pS => fS
                 | pAdd => fAdd
                 | pPair => fPair
                 | pFst => fFst
                 | pSnd => fSnd
                 end))%option.

Definition orb_pident (f : pident -> bool) : bool
  := (f pO || f pS || f pAdd || f pPair || f pFst || f pSnd)%bool.
Definition or_opt_pident {T} (f : pident -> option T) : bool
  := orb_pident (fun p => match f p with Some _ => true | None => false end).

Definition pident_of_ident {t} (idc : ident t) : pident
  := match idc with
     | O => pO
     | S => pS
     | Add => pAdd
     | Pair A B => pPair
     | Fst A B => pFst
     | Snd A B => pSnd
     end.

Definition reveal_rawexpr_cps {T}
           (k : rawexpr -> T)
           (e : rawexpr)
  : T
  := match e with
     | rExpr t e
       => match e with
          | Ident t idc => k (rIdent idc e)
          | App s d f x => k (rApp (rExpr f) (rExpr x) e)
          | Literal n => k (rLiteral n e)
          end
     | e' => k e'
     end.

Fixpoint binding_dataT (p : pattern)
  := match p return Type with
     | Wildcard None => anyexpr
     | Wildcard (Some t) => expr t
     | pIdent _ => unit
     | pApp f x => binding_dataT f * binding_dataT x
     | pLiteral => nat
     end%type.

Fixpoint bind_data_cps {T} (e : rawexpr) (p : pattern) {struct p}
  : (option (binding_dataT p) -> T) -> T
  := match p return (option (binding_dataT p) -> T) -> T with
     | Wildcard None
       => fun k => k (Some (wrap (expr_of_rawexpr e)))
     | Wildcard (Some _)
       => fun k => type.try_transport_cps _ _ _ (expr_of_rawexpr e) k
     | pIdent pidc
       => fun k
          => match e with
             | rIdent t idc _ _
               => if pident_ident_beq pidc idc
                  then k (Some tt)
                  else k None
             | _ => k None
             end
     | pApp pf px
       => fun k
          => match e with
             | rApp f x _ _
               => @bind_data_cps
                    T f pf
                    (fun f'
                     => match f' with
                        | Some f''
                          => @bind_data_cps
                               T x px
                               (fun x'
                                => match x' with
                                   | Some x''
                                     => k (Some (f'', x''))
                                   | None => k None
                                   end)
                        | None => k None
                        end)
             | _ => k None
             end
     | pLiteral
       => fun k
          => match e with
             | rLiteral n _ _
               => k (Some n)
             | _ => k None
             end
     end.

Inductive decision_tree :=
| TryLeaf (k : nat) (onfailure : decision_tree)
| Failure
| Switch (icases : pident -> option decision_tree)
         (app_case : option decision_tree)
         (lit_case : option decision_tree)
         (default : decision_tree)
| Swap (i : nat) (cont : decision_tree).

Definition swap_list {A} (i j : nat) (ls : list A) : option (list A)
  := match nth_error ls i, nth_error ls j with
     | Some vi, Some vj => Some (set_nth i vj (set_nth j vi ls))
     | _, _ => None
     end.

Fixpoint eval_decision_tree {T} (ctx : list rawexpr) (d : decision_tree) (cont : option nat -> list rawexpr -> option (unit -> T) -> T) {struct d} : T
  := match d with
     | TryLeaf k onfailure
       => cont (Some k) ctx
               (Some (fun 'tt => @eval_decision_tree T ctx onfailure cont))
     | Failure => cont None ctx None
     | Switch icases app_case lit_case default_case
       => let do_literal := match lit_case with Some _ => true | None => false end in
          let default _ := @eval_decision_tree T ctx default_case cont in
          match ctx with
          | nil => cont None ctx None
          | ctx0 :: ctx'
            => reveal_rawexpr_cps
                 (fun ctx0'
                  => match ctx0' with
                     | rIdent t idc t' alt
                       => if or_opt_pident icases
                          then eta_ident_cps
                                 idc
                                 (fun _ idc'
                                  => match icases (pident_of_ident idc') with
                                     | Some icase
                                       => @eval_decision_tree
                                            T ctx' icase
                                            (fun k ctx''
                                             => cont k (rIdent idc' alt :: ctx''))
                                     | None => default tt
                                     end)
                          else default tt
                     | rApp f x t alt
                       => match app_case with
                          | Some app_case
                            => @eval_decision_tree
                                 T (f :: x :: ctx') app_case
                                 (fun k ctx''
                                  => match ctx'' with
                                     | f' :: x' :: ctx'''
                                       => cont k (rApp f' x' alt :: ctx''')
                                     | _ => cont None ctx
                                     end)
                          | None => default tt
                          end
                     | rLiteral n t alt
                       => match lit_case with
                          | Some lit_case
                            => @eval_decision_tree
                                 T ctx' lit_case
                                 (fun k ctx''
                                  => cont k (rLiteral n alt :: ctx''))
                          | None => default tt
                          end
                     | rExpr t e
                       => (* impossible *) cont None ctx None
                     end)
                 ctx0
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
           (rew : list { p : pattern & binding_dataT p -> option anyexpr })
           (e : expr (Base t))
  : expr (Base t)
  := eval_decision_tree
       (rExpr e::nil) d
       (fun k ctx default_on_rewrite_failure
        => match k, ctx with
           | Some k', e'::nil
             => match nth_error rew k' with
                | Some (existT p f)
                  => bind_data_cps
                       e' p
                       (fun v
                        => match option_map f v with
                           | Some (Some fv)
                             => type.try_transport_cps
                                  _ _ _ (unwrap fv)
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

Definition get_index_of_first_non_wildcard (p : list pattern) : option nat
  := first_satisfying_helper
       (fun '(n, x) => match x with
                       | Wildcard _ => None
                       | _ => Some n
                       end)
       (enumerate p).

Definition filter_pattern_wildcard (p : list (nat * list pattern)) : list (nat * list pattern)
  := filter (fun '(_, p) => match p with
                            | Wildcard _::_ => true
                            | _ => false
                            end)
            p.

Definition contains_pattern_literal (p : list (nat * list pattern)) : bool
  := existsb (fun '(n, p) => match p with
                             | pLiteral::_ => true
                             | _ => false
                             end)
             p.

Definition contains_pattern_pident (pidc : pident) (p : list (nat * list pattern)) : bool
  := existsb (fun '(n, p) => match p with
                             | pIdent pidc'::_ => pident_beq pidc pidc'
                             | _ => false
                             end)
             p.

Definition contains_pattern_app (p : list (nat * list pattern)) : bool
  := existsb (fun '(n, p) => match p with
                             | pApp _ _::_ => true
                             | _ => false
                             end)
             p.

Definition refine_pattern_literal (p : nat * list pattern) : option (nat * list pattern)
  := match p with
     | (n, Wildcard _::ps)
     | (n, pLiteral::ps)
       => Some (n, ps)
     | (_, pIdent _::_)
     | (_, pApp _ _::_)
     | (_, nil)
       => None
     end.

Definition refine_pattern_app (p : nat * list pattern) : option (nat * list pattern)
  := match p with
     | (n, Wildcard _::ps)
       => Some (n, Wildcard None :: Wildcard None :: ps)
     | (n, pApp f x :: ps)
       => Some (n, f :: x :: ps)
     | (_, pLiteral::_)
     | (_, pIdent _::_)
     | (_, nil)
       => None
     end.

Definition refine_pattern_pident (pidc : pident) (p : nat * list pattern) : option (nat * list pattern)
  := match p with
     | (n, Wildcard _::ps)
       => Some (n, ps)
     | (n, pIdent pidc'::ps)
       => if pident_beq pidc pidc'
          then Some (n, ps)
          else None
     | (_, pApp _ _::_)
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
            => default_case <- compile_rewrites (filter_pattern_wildcard pattern_matrix);
                 lit_case <- (if contains_pattern_literal pattern_matrix
                              then option_map Some (compile_rewrites (omap refine_pattern_literal pattern_matrix))
                              else Some None);
                 app_case <- (if contains_pattern_app pattern_matrix
                              then option_map Some (compile_rewrites (omap refine_pattern_app pattern_matrix))
                              else Some None);
                 icases
                   <- (if orb_pident (fun pidc => contains_pattern_pident pidc pattern_matrix)
                       then eta_option_pident_cps
                              (fun pidc => if contains_pattern_pident pidc pattern_matrix
                                           then option_map Some (compile_rewrites (omap (refine_pattern_pident pidc) pattern_matrix))
                                           else Some None)
                       else Some (fun _ => None));
                 Some (Switch icases app_case lit_case default_case)
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

Definition compile_rewrites (fuel : nat) (ps : list { p : pattern & binding_dataT p -> option anyexpr })
  := compile_rewrites' fuel (enumerate (List.map (fun p => projT1 p :: nil) ps)).

Fixpoint with_bindingsT (p : pattern) (T : Type)
  := match p with
     | Wildcard (Some t) => expr t -> T
     | Wildcard None => forall t, expr t -> T
     | pLiteral => nat -> T
     | pApp f x => with_bindingsT f (with_bindingsT x T)
     | pIdent _ => T
     end.

Fixpoint lift_with_bindings {p A B} (F : A -> B) {struct p} : with_bindingsT p A -> with_bindingsT p B
  := match p return with_bindingsT p A -> with_bindingsT p B with
     | Wildcard (Some _) => fun f e => F (f e)
     | Wildcard None => fun f _ e => F (f _ e)
     | pLiteral => fun f e => F (f e)
     | pApp f x
       => @lift_with_bindings
            f _ _
            (@lift_with_bindings x _ _ F)
     | pIdent _
       => F
     end.

Fixpoint app_binding_data {T p} : forall (f : with_bindingsT p T) (v : binding_dataT p), T
  := match p return forall (f : with_bindingsT p T) (v : binding_dataT p), T with
     | Wildcard (Some _)
     | pLiteral
       => fun f => f
     | Wildcard None
       => fun f v => f _ (unwrap v)
     | pApp f x
       => fun F '(vf, vx)
          => @app_binding_data _ x (@app_binding_data _ f F vf) vx
     | pIdent _
       => fun f 'tt => f
     end.

Notation make_rewrite' p f
 := (existT
       (fun p' : pattern => binding_dataT p' -> option anyexpr)
       p%pattern
       (@app_binding_data _ p%pattern f%expr)).
Notation make_rewrite p f
  := (let f' := (@lift_with_bindings p _ _ (fun x:anyexpr => Some x) f%expr) in
      make_rewrite' p f').

Definition rewrite_rules : list { p : pattern & binding_dataT p -> option anyexpr }
  := [make_rewrite (0 + ??ℕ) (fun x => x);
        make_rewrite (??ℕ + 0) (fun x => x);
        make_rewrite (#? + #?) (fun x y => ##(x + y));
        make_rewrite (??ℕ.+1 + ??ℕ.+1) (fun x y => (x+y).+1.+1);
        make_rewrite (??ℕ.+1 + ??ℕ) (fun x y => (x+y).+1);
        make_rewrite (??ℕ + ??ℕ.+1) (fun x y => (x+y).+1);
        make_rewrite (#pFst @ (??, ??)) (fun tx x ty y => x);
        make_rewrite (#pSnd @ (??, ??)) (fun tx x ty y => y)
     ]%list%pattern.

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
Definition dorewrite1 {t} (e : expr (Base t)) : expr (Base t)
  := eval_rewrite_rules dtree rewrite_rules e.

Fixpoint value (t : type)
  := match t with
     | Base _ as t
       => expr t
     | Arrow s d => expr s -> value d
     end.

Fixpoint do_rewrite_ident {t} : expr t -> value t
  := match t return expr t -> value t with
     | Base _
       => fun e => dorewrite1 e
     | Arrow s d
       => fun f x => @do_rewrite_ident d (f @ x)%expr
     end.

Fixpoint dorewrite' {t} (e : expr t) : value t
  := match e in expr t return value t with
     | Ident t idc
       => eta_ident_cps idc (fun _ idc' => do_rewrite_ident #idc')
     | App s d f x => @dorewrite' _ f (@dorewrite' _ x)
     | Literal _ as e => e
     end.

Arguments bind_data_cps / .
Arguments dorewrite1 / .
Arguments dorewrite' / .
Arguments do_rewrite_ident / .
Arguments rewrite_rules / .
(*Arguments domatch / .*)
Arguments eval_rewrite_rules / .
Arguments dtree / .
Arguments eval_decision_tree / .
Arguments eta_ident_cps / .
Arguments eta_option_pident_cps / .
Arguments pident_of_ident / .
Arguments option_map _ _ _ !_ / .
Arguments swap_list _ !_ !_ !_ / .
Arguments set_nth _ !_ _ !_ / .
Arguments lift_with_bindings / .
Arguments app_binding_data / .
Arguments anyexpr_ty / .
Arguments unwrap / .
Arguments type_of_rawexpr / .
Arguments expr_of_rawexpr / .
Arguments reveal_rawexpr_cps / .
Arguments type.try_transport_base_cps _ _ !_ !_ / .
Arguments orb_pident / .
Arguments or_opt_pident / .
Definition dorewrite''
  := Eval cbv (*-[type.try_transport_base_cps value]*) (* but we also need to exclude things in the rhs of the rewrite rule *)
          [dorewrite' eta_ident_cps do_rewrite_ident dorewrite1 dtree eval_rewrite_rules reveal_rawexpr_cps or_opt_pident orb_pident orb eta_ident_cps pident_of_ident anyexpr_ty eval_decision_tree nth_error rewrite_rules pident_ident_beq option_map expr_of_rawexpr type_of_rawexpr bind_data_cps type.try_transport_cps app_binding_data lift_with_bindings swap_list set_nth update_nth unwrap binding_dataT]
    in @dorewrite'.
Arguments dorewrite'' / .
Definition dorewrite
  := Eval cbn [dorewrite'' type.try_transport_base_cps Option.bind] in @dorewrite''.
Arguments dorewrite {t} e.
Local Open Scope expr_scope.
Print dorewrite.
(*dorewrite =
fix dorewrite' (t : type) (e : expr t) {struct e} :
value t :=
  match e in (expr t0) return (value t0) with
  | #(idc) =>
      match idc in (ident t1) return (value t1) with
      | O => 0
      | S => fun x : expr Nat => x.+1
      | Add =>
          fun x x0 : expr Nat =>
          match x with
          | 0 => x0
          | @App s _ f x1 =>
              match x0 with
              | 0 => x
              | @App s0 _ #(S) x2 =>
                  match f with
                  | #(S) =>
                      type.try_transport_base_cps
                        (fun x3 : base_type => expr x3) s Nat x1
                        (fun x' : option (expr Nat) =>
                         match x' with
                         | Some x'' =>
                             type.try_transport_base_cps
                               (fun x3 : base_type => expr x3) s0 Nat x2
                               (fun x'0 : option (expr Nat) =>
                                match x'0 with
                                | Some x''0 => ((x'' + x''0).+1).+1
                                | None => x + x0
                                end)
                         | None => x + x0
                         end)
                  | _ @ _ =>
                      type.try_transport_base_cps
                        (fun x4 : base_type => expr x4) s0 Nat x2
                        (fun x' : option (expr Nat) =>
                         match x' with
                         | Some x'' => (x + x'').+1
                         | None => x + x0
                         end)
                  | _ =>
                      type.try_transport_base_cps
                        (fun x3 : base_type => expr x3) s0 Nat x2
                        (fun x' : option (expr Nat) =>
                         match x' with
                         | Some x'' => (x + x'').+1
                         | None => x + x0
                         end)
                  end
              | @App s0 _ (_ @ _) _ =>
                  match f with
                  | #(S) =>
                      type.try_transport_base_cps
                        (fun x4 : base_type => expr x4) s Nat x1
                        (fun x' : option (expr Nat) =>
                         match x' with
                         | Some x'' => (x'' + x0).+1
                         | None => x + x0
                         end)
                  | _ => x + x0
                  end
              | @App s0 _ 0 _ | @App s0 _ #(Add) _ | @App s0 _ #
                (@Pair _ _) _ | @App s0 _ #(@Fst _ _) _ | @App s0 _
                #(@Snd _ _) _ | @App s0 _ ##(_) _ =>
                  match f with
                  | #(S) =>
                      type.try_transport_base_cps
                        (fun x3 : base_type => expr x3) s Nat x1
                        (fun x' : option (expr Nat) =>
                         match x' with
                         | Some x'' => (x'' + x0).+1
                         | None => x + x0
                         end)
                  | _ => x + x0
                  end
              | _ =>
                  match f with
                  | #(S) =>
                      type.try_transport_base_cps
                        (fun x2 : base_type => expr x2) s Nat x1
                        (fun x' : option (expr Nat) =>
                         match x' with
                         | Some x'' => (x'' + x0).+1
                         | None => x + x0
                         end)
                  | _ => x + x0
                  end
              end
          | ##(n) =>
              match x0 with
              | 0 => x
              | @App s _ #(S) x1 =>
                  type.try_transport_base_cps (fun x2 : base_type => expr x2)
                    s Nat x1
                    (fun x' : option (expr Nat) =>
                     match x' with
                     | Some x'' => (x + x'').+1
                     | None => x + x0
                     end)
              | @App s _ 0 _ | @App s _ #(Add) _ | @App s _ #
                (@Pair _ _) _ | @App s _ #(@Fst _ _) _ | @App s _ #
                (@Snd _ _) _ | @App s _ (_ @ _) _ | @App s _ ##
                (_) _ => x + x0
              | ##(n0) => ##(n + n0)
              | _ => x + x0
              end
          | _ =>
              match x0 with
              | 0 => x
              | @App s _ #(S) x1 =>
                  type.try_transport_base_cps (fun x2 : base_type => expr x2)
                    s Nat x1
                    (fun x' : option (expr Nat) =>
                     match x' with
                     | Some x'' => (x + x'').+1
                     | None => x + x0
                     end)
              | @App s _ 0 _ | @App s _ #(Add) _ | @App s _ #
                (@Pair _ _) _ | @App s _ #(@Fst _ _) _ | @App s _ #
                (@Snd _ _) _ | @App s _ (_ @ _) _ | @App s _ ##
                (_) _ => x + x0
              | _ => x + x0
              end
          end
      | @Pair A B => fun (x : expr A) (x0 : expr B) => (x, x0)
      | @Fst A B =>
          fun x : expr (A * B) =>
          match x with
          | @App s0 _ #(@Pair _ _) x1 @ _ =>
              type.try_transport_base_cps (fun x2 : base_type => expr x2) s0 A
                x1
                (fun fv : option (expr A) =>
                 match fv with
                 | Some fv0 => fv0
                 | None => #(Fst) @ x
                 end)
          | @App s0 _ 0 _ @ _ | @App s0 _ #(S) _ @ _ |
            @App s0 _ #(Add) _ @ _ | @App s0 _ #(@Fst _ _) _ @ _ |
            @App s0 _ #(@Snd _ _) _ @ _ | @App s0 _ (_ @ _) _ @ _ |
            @App s0 _ ##(_) _ @ _ => #(Fst) @ x
          | _ => #(Fst) @ x
          end
      | @Snd A B =>
          fun x : expr (A * B) =>
          match x with
          | @App s _ (#(@Pair _ _) @ _) x0 =>
              type.try_transport_base_cps (fun x2 : base_type => expr x2) s B
                x0
                (fun fv : option (expr B) =>
                 match fv with
                 | Some fv0 => fv0
                 | None => #(Snd) @ x
                 end)
          | @App s _ #(_) _ | @App s _ (0 @ _) _ | @App s _
            (_.+1) _ | @App s _ (#(Add) @ _) _ | @App s _
            (#(@Fst _ _) @ _) _ | @App s _ (#(@Snd _ _) @ _) _ | @App s _
            (_ @ _ @ _) _ | @App s _ (##(_) @ _) _ | @App s _ ##
            (_) _ => #(Snd) @ x
          | _ => #(Snd) @ x
          end
      end
  | @App s d f x => dorewrite' (s -> d)%ctype f (dorewrite' s x)
  | ##(n) => ##(n)
  end
     : forall t : type, expr t -> value t

Argument t is implicit and maximally inserted
Argument scopes are [ctype_scope expr_scope]
*)
