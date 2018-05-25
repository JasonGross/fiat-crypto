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
  Fixpoint for_each_lhs_of_arrow (f : type -> Set) (t : type) : Set
    := match t with
       | Nat => unit
       | Arrow s d => f s * for_each_lhs_of_arrow f d
       end.
  Inductive for_each_lhs_of_arrow_ind (f : type -> Set) : type -> Set :=
  | NoLHS : for_each_lhs_of_arrow_ind f Nat
  | ArrowLHS {s d} (_ : f s) (_ : for_each_lhs_of_arrow_ind f d) : for_each_lhs_of_arrow_ind f (s -> d).
  Global Arguments NoLHS {_}.
  Global Arguments ArrowLHS {_ _ _} _ _.

  Definition invert_for_each_lhs_of_arrow_ind {f t} (x : for_each_lhs_of_arrow_ind f t)
    : match t with
      | Nat => unit
      | Arrow s d => f s * for_each_lhs_of_arrow_ind f d
      end%type
    := match x with
       | NoLHS => tt
       | ArrowLHS _ _ x xs => (x, xs)
       end.

  Fixpoint for_each_lhs_of_arrow_of_ind {f : type -> Set} {t : type}
    : for_each_lhs_of_arrow_ind f t -> for_each_lhs_of_arrow f t
    := match t with
       | Nat => invert_for_each_lhs_of_arrow_ind
       | Arrow s d
         => fun x
            => let '(x, xs) := invert_for_each_lhs_of_arrow_ind x in
               (x, @for_each_lhs_of_arrow_of_ind f d xs)
       end.

  Global Coercion for_each_lhs_of_arrow_of_ind : for_each_lhs_of_arrow_ind >-> for_each_lhs_of_arrow.

  Fixpoint fold_for_each_lhs_of_arrow {f : type -> Set} (F : forall t, f t -> Type) {t}
    : for_each_lhs_of_arrow f t -> Type
    := match t return for_each_lhs_of_arrow f t -> Type with
       | Nat => fun _ => unit
       | Arrow s d
         => fun '(x, xs)
            => F _ x * @fold_for_each_lhs_of_arrow f F d xs
       end%type.

  Fixpoint bind_for_each_lhs_of_arrowT {f : type -> Set} (F : forall t, f t -> Type -> Type) {t}
    : for_each_lhs_of_arrow f t -> Type -> Type
    := match t return for_each_lhs_of_arrow f t -> Type -> Type with
       | Nat => fun _ T => T
       | Arrow s d
         => fun '(x, xs) T
            => F _ x (@bind_for_each_lhs_of_arrowT f F d xs T)
       end%type.

  Section fold_for_each_lhs_of_arrow.
    Context {f : type -> Set}
            (F : forall t, f t -> Type).
    Fixpoint fold_for_each_lhs_of_arrow_ind {t} (xs : for_each_lhs_of_arrow_ind f t) : Type
      := match xs return Type with
         | NoLHS => unit
         | ArrowLHS s d x xs
           => F _ x * @fold_for_each_lhs_of_arrow_ind d xs
         end.
  End fold_for_each_lhs_of_arrow.
  Section bind_for_each_lhs_of_arrow.
    Context {f : type -> Set}
            (F : forall t, f t -> Type -> Type)
            (T : Type).
    Fixpoint bind_for_each_lhs_of_arrow_indT {t} (xs : for_each_lhs_of_arrow_ind f t)
      : Type
      := match xs with
         | NoLHS => T
         | ArrowLHS s d x xs
           => F _ x (@bind_for_each_lhs_of_arrow_indT d xs)
         end%type.

    Section app.
      Context (F' : forall t, f t -> Type)
              (APP : forall t ft T, F t ft T -> F' t ft -> T).
      Fixpoint app_fold_for_each_lhs_of_arrow_ind
               {t} {xs : for_each_lhs_of_arrow_ind f t}
        : bind_for_each_lhs_of_arrow_indT xs -> fold_for_each_lhs_of_arrow_ind F' xs -> T
        := match xs return bind_for_each_lhs_of_arrow_indT xs -> fold_for_each_lhs_of_arrow_ind F' xs -> T with
           | NoLHS => fun v _ => v
           | ArrowLHS s d x xs
             => fun G '(v, vs)
                => @app_fold_for_each_lhs_of_arrow_ind d xs (APP _ _ _ G v) vs
           end.
    End app.
  End bind_for_each_lhs_of_arrow.
  Section bind_for_each_lhs_of_arrow2.
    Context {f : type -> Set}
            (F : forall t, f t -> Type -> Type)
            {A B : Type}
            (G : A -> B)
            (lift_G : forall t ft A B, (A -> B) -> F t ft A -> F t ft B).
    Fixpoint lift_bind_for_each_lhs_of_arrow_indT
             {t} (xs : for_each_lhs_of_arrow_ind f t)
      : bind_for_each_lhs_of_arrow_indT F A xs -> bind_for_each_lhs_of_arrow_indT F B xs
      := match xs return bind_for_each_lhs_of_arrow_indT F A xs -> bind_for_each_lhs_of_arrow_indT F B xs with
         | NoLHS => G
         | ArrowLHS s d x xs
           => lift_G
                _ _ _ _
                (@lift_bind_for_each_lhs_of_arrow_indT d xs)
         end%type.
  End bind_for_each_lhs_of_arrow2.

  Fixpoint const_for_each_lhs_of_arrow {P : type -> Set} (v : forall t, P t) {t} : for_each_lhs_of_arrow P t
    := match t with
       | Nat => tt
       | Arrow s d => (v s, @const_for_each_lhs_of_arrow P v d)
       end.

  Fixpoint try_transport_cps {T} (P : type -> Type) (t1 t2 : type) {struct t2} : P t1 -> (option (P t2) -> T) -> T
    := match t2 with
       | Nat
         => fun v k
            => match t1 with
               | Nat => fun v => k (Some v)
               | _ => fun _ => k None
               end v
       | Arrow s d
         => fun v k
            => match t1 return P t1 -> _ with
               | Arrow s' d'
                 => fun v
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
               | _ => fun _ => k None
               end v
       end.

  Fixpoint try_transport_cps' {T} (P : type -> Type) (t1 t2 : type) {struct t1} : P t1 -> (option (P t2) -> T) -> T
    := match t1, t2 with
       | Nat, Nat => fun v k => k (Some v)
       | Arrow s d, Arrow s' d'
         => fun v k
            => try_transport_cps'
                 (fun s => P (Arrow s _)) _ _ v
                 (fun v'
                  => match v' with
                     | Some v'
                       => try_transport_cps'
                            (fun d => P (Arrow _ d)) _ _ v'
                            k
                     | None => k None
                     end)
       | Nat, _
       | Arrow _ _, _
         => fun _ k => k None
       end.
End type.
Global Coercion type.for_each_lhs_of_arrow_of_ind : type.for_each_lhs_of_arrow_ind >-> type.for_each_lhs_of_arrow.
Bind Scope for_each_lhs_of_arrow_scope with type.for_each_lhs_of_arrow_ind.
Delimit Scope for_each_lhs_of_arrow_scope with for_each_lhs_of_arrow.
Notation "[ ]" := type.NoLHS : for_each_lhs_of_arrow_scope.
Notation "[ x ]" := (type.ArrowLHS x type.NoLHS) : for_each_lhs_of_arrow_scope.
Notation "[ x ; y ; .. ; z ]" :=  (type.ArrowLHS x (type.ArrowLHS y .. (type.ArrowLHS z type.NoLHS) ..)) : for_each_lhs_of_arrow_scope.

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

Inductive pattern : Set :=
| Wildcard
| pLiteral
| pAppIdent {t} (idc : ident t) (args : type.for_each_lhs_of_arrow_ind (fun _ => pattern) t).

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
Notation "#?" := pLiteral : pattern_scope.
Notation "??" := Wildcard : pattern_scope.
Notation "0" := (pAppIdent O [])%pattern : pattern_scope.
Notation "n '.+1'" := (pAppIdent S [n])%pattern (at level 10, format "n '.+1'") : pattern_scope.
Notation "x + y" := (pAppIdent Add [x; y])%pattern : pattern_scope.

(* urgh, this is ident-specific, and probably should not be ... *)
Definition mkapp_from_context {t} (idc : ident t) (ctx : list (expr Nat))
  : option (list (expr Nat))
  := match idc, ctx with
     | O as idc, ctx' => Some ((#idc) :: ctx')
     | S as idc, x :: ctx' => Some ((#idc @ x) :: ctx')
     | Add as idc, x :: y :: ctx' => Some ((#idc @ x @ y) :: ctx')
     | S, _
     | Add, _
       => None
     end%expr.

(* we cheat to get that every argument is nat *)
Definition unmkapp_to_context {t P} (idc : ident t) (args : type.for_each_lhs_of_arrow P t) (ctx : list (P Nat))
  : list (P Nat)
  := match idc in ident t return type.for_each_lhs_of_arrow P t -> list (P Nat) with
     | O => fun _ => ctx
     | S => fun '(x, _) => x :: ctx
     | Add => fun '(x, (y, _)) => x :: y :: ctx
     end args.

Record > anyexpr := wrap { anyexpr_ty : type ; unwrap :> expr anyexpr_ty }.
Arguments wrap {_} _.

Fixpoint invert_AppIdent_cps {T t} (e : expr t) (args : type.for_each_lhs_of_arrow expr t) {struct e} : (option { t' : _ & ident t' * type.for_each_lhs_of_arrow expr t' }%type -> T) -> T
  := match e in expr t return type.for_each_lhs_of_arrow expr t -> (option _ -> T) -> T with
     | Ident t idc
       => fun args k
          => k (Some (existT (fun t' => ident t' * type.for_each_lhs_of_arrow expr t')%type
                             t (idc, args)))
     | App s d f x
       => fun args => @invert_AppIdent_cps _ _ f (x, args)
     | Literal n => fun _ k => k None
     end args.

(*
Fixpoint invert_AppIdentOrLiteral_cps' {T t} (e : expr t) (args : type.for_each_lhs_of_arrow expr t)
         (T0 := { t' : _ & ident t' * type.for_each_lhs_of_arrow expr t' }%type)
         {struct e}
  : (T0 + match t with
          | Nat => nat
          | Arrow _ _ => Empty_set
          end%type
     -> T) -> T
  := match e in expr t
           return type.for_each_lhs_of_arrow expr t
                  -> ((T0
                       + match t with
                         | Nat => nat
                         | Arrow _ _ => Empty_set
                         end%type
                       -> T) -> T) with
     | Ident t idc
       => fun args k
          => k (inl (existT (fun t' => ident t' * type.for_each_lhs_of_arrow expr t')%type
                            t (idc, args)))
     | App s d f x
       => fun args k
          => @invert_AppIdentOrLiteral_cps
               _ _ f (x, args)
               (fun v
                => match v with
                   | inl v => k (inl v)
                   | inr v => match v with end
                   end)
     | Literal n => fun _ k => k (inr n)
     end args.
*)
(* we want to eta-expand on actually possible identifiers *)
Definition invert_AppIdentOrLiteral_cps {T} (e : expr Nat) (args : type.for_each_lhs_of_arrow expr Nat)
           (T0P := fun t' => (ident t' * type.for_each_lhs_of_arrow expr t')%type)
           (T0 := sigT T0P)
           (k : option (T0 + nat) -> T)
  : T
  := match e with
     | Literal n => k (Some (inr n))
     | #O => k (Some (inl (existT T0P _ (O, tt))))
     | #S @ x
       => type.try_transport_cps
            _ _ _ x
            (fun x' => match x' with
                       | Some x' => k (Some (inl (existT T0P _ (S, (x', tt)))))
                       | None => k None
                       end)
     | #Add @ x @ y
       => type.try_transport_cps
            _ _ _ x
            (fun x'
             => type.try_transport_cps
                  _ _ _ y
                  (fun y'
                   => match x', y' with
                      | Some x', Some y'
                        => k (Some (inl (existT T0P _ (Add, (x', (y', tt))))))
                      | _, _ => k None
                      end))
     | _ => k None (* impossible *)
     end%expr%option.

Definition hlist {A} (f : A -> Set) (ls : list A)
  := fold_right
       (fun a b : Set => prod a b)
       unit
       (map f ls).

Fixpoint binding_dataT (p : pattern)
  := match p return Type with
     | Wildcard => expr Nat
     | pLiteral => nat
     | pAppIdent t idc args => type.fold_for_each_lhs_of_arrow_ind (fun _ => binding_dataT) args
     end%type.

Section bind_data_cps_helper.
  Context {T}
          (bind_data_cps : forall {t} (e : expr t) (p : pattern),
              (option (binding_dataT p) -> T) -> T).

  Fixpoint bind_for_each_lhs_of_arrow_data_cps
           {t}
           (pargs : type.for_each_lhs_of_arrow_ind (fun _ => pattern) t)
    : forall (args : type.for_each_lhs_of_arrow expr t)
             (k : option
                    (type.fold_for_each_lhs_of_arrow_ind (fun _ : type => binding_dataT)
                                                         pargs) -> T),
      T
    := match pargs in type.for_each_lhs_of_arrow_ind _ t
             return (forall (args : type.for_each_lhs_of_arrow expr t)
                            (k : option
                                   (type.fold_for_each_lhs_of_arrow_ind (fun _ : type => binding_dataT)
                                                                        pargs) -> T),
                        T)
       with
       | type.NoLHS => fun tt k => k (Some tt)
       | type.ArrowLHS s d x xs
         => fun '(y, ys) k
            => @bind_data_cps
                 s y x
                 (fun y'
                  => @bind_for_each_lhs_of_arrow_data_cps
                       d xs ys
                       (fun ys'
                        => k (y' <- y'; ys' <- ys'; Some (y', ys'))%option))
       end.
End bind_data_cps_helper.

Fixpoint bind_data_cps {T t} (e : expr t) (p : pattern) {struct p}
  : (option (binding_dataT p) -> T) -> T
  := match p return (option (binding_dataT p) -> T) -> T with
     | Wildcard
       => fun k => type.try_transport_cps _ _ _ e k
     | pLiteral
       => fun k
          => match e with
             | Literal n => k (Some n)
             | _ => k None
             end
     | pAppIdent pt pidc pargs
       => fun k
          => type.try_transport_cps
               _ _ _ e
               (fun e' : option (expr Nat)
                => match e' with
                   | Some e'
                     => invert_AppIdent_cps
                          e' tt
                          (fun e'
                           => match e' with
                              | Some (existT t (idc, args))
                                => type.try_transport_cps
                                     _ _ _ args
                                     (fun args'
                                      => match args' with
                                         | Some args'
                                           => bind_for_each_lhs_of_arrow_data_cps
                                                (@bind_data_cps T)
                                                pargs args' k
                                         | None => k None
                                         end)
                              | None => k None
                              end)
                   | None => k None
                   end)
     end.

Fixpoint domatch {t} (ps : list { p : pattern & { t' : type & binding_dataT p -> option (expr t') } })
         (e : expr t)
  : expr t
  := match ps with
     | nil => e
     | existT p (existT _ f) :: ps
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
| Switch (icases : forall t, ident t -> decision_tree)
         (lit_case : decision_tree)
| Swap (i : nat) (cont : decision_tree).

Definition swap_list {A} (i j : nat) (ls : list A) : option (list A)
  := match nth_error ls i, nth_error ls j with
     | Some vi, Some vj => Some (set_nth i vj (set_nth j vi ls))
     | _, _ => None
     end.

Fixpoint eval_decision_tree {T} (ctx : list (expr Nat)) (d : decision_tree) (cont : option nat -> list (expr Nat) -> option (unit -> T) -> T) {struct d} : T
  := match d with
     | TryLeaf k onfailure
       => cont (Some k) ctx
               (Some (fun 'tt => @eval_decision_tree T ctx onfailure cont))
     | Failure => cont None ctx None
     | Switch icases lit_case
       => match ctx with
          | nil => cont None ctx None
          | ctx0 :: ctx'
            => invert_AppIdentOrLiteral_cps
                 ctx0 tt
                 (fun ctx0'
                  => match ctx0' with
                     | Some (inr n) (* Literal *)
                       => @eval_decision_tree
                            T ctx' lit_case
                            (fun k ctx''
                             => cont k (Literal n :: ctx''))
                     | Some (inl (existT _ (idc, args)))
                       => @eval_decision_tree
                            T (unmkapp_to_context idc args ctx') (icases _ idc)
                            (fun k ctx''
                             => match mkapp_from_context idc ctx'' with
                                | Some ctx'''
                                  => cont k ctx'''
                                | None => cont None ctx
                                end)
                     | None
                       => cont None ctx None
                     end)
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
           (rew : list { p : pattern & { t' : type & binding_dataT p -> option (expr t') } })
           (e : expr Nat)
  : expr Nat
  := eval_decision_tree
       (e::nil) d
       (fun k ctx default_on_rewrite_failure
        => match k, ctx with
           | Some k', e'::nil
             => match nth_error rew k' with
                | Some (existT p (existT _ f))
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
     | (_, pAppIdent _ _ _::_)
     | (_, nil)
       => None
     end.

Definition refine_pattern_app_ident {t} (idc : ident t) (p : nat * list pattern) : option (nat * list pattern)
  := match p with
     | (n, Wildcard::ps)
       => let p' := unmkapp_to_context idc (type.const_for_each_lhs_of_arrow (fun _ => Wildcard)) ps in
          Some (n, p')
     | (n, pAppIdent _ idc' pargs::ps)
       => ident_beq_cps
            idc idc'
            (fun b
             => if b
                then
                  type.try_transport_cps
                    (type.for_each_lhs_of_arrow_ind _) _ _ pargs
                    (fun pargs'
                     => (pargs' <- pargs';
                           let p' := unmkapp_to_context idc pargs' ps in
                           Some (n, p')))
                else None)
     | (_, pLiteral::_)
     | (_, nil)
       => None
     end%option.

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
                 icases
                   <- (eta_option_ident_cps
                         (fun _ idc => compile_rewrites (omap (refine_pattern_app_ident idc) pattern_matrix)));
                 Some (Switch icases lit_case)
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
     | Wildcard => expr Nat -> T
     | pLiteral => nat -> T
     | pAppIdent _ idc args
       => type.bind_for_each_lhs_of_arrow_indT (fun _ => with_bindingsT) T args
     end.

Fixpoint lift_with_bindings {p A B} (F : A -> B) {struct p} : with_bindingsT p A -> with_bindingsT p B
  := match p return with_bindingsT p A -> with_bindingsT p B with
     | Wildcard => fun f e => F (f e)
     | pLiteral => fun f e => F (f e)
     | pAppIdent t idc args
       => type.lift_bind_for_each_lhs_of_arrow_indT
            _ F (fun _ => @lift_with_bindings) args
     end.

Fixpoint app_binding_data {T p} : forall (f : with_bindingsT p T) (v : binding_dataT p), T
  := match p return forall (f : with_bindingsT p T) (v : binding_dataT p), T with
     | Wildcard
     | pLiteral
       => fun f => f
     | pAppIdent t idc pargs
       => type.app_fold_for_each_lhs_of_arrow_ind
            _ _ _ (fun _ _ T => @app_binding_data T _)
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
  := [make_rewrite (0 + ??) (fun x => x);
        make_rewrite (?? + 0) (fun x => x);
        make_rewrite (#? + #?) (fun x y => ##(x + y));
        make_rewrite (??.+1 + ??) (fun x y => (x+y).+1);
        make_rewrite (?? + ??.+1) (fun x y => (x+y).+1)]%list.

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
Definition dorewrite1 (e : expr Nat) : expr Nat
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
Arguments eta_option_ident_cps / .
Arguments option_map _ _ _ !_ / .
Arguments swap_list _ !_ !_ !_ / .
Arguments set_nth _ !_ _ !_ / .
Arguments lift_with_bindings / .
Arguments app_binding_data / .
Arguments do_rewrite_ident / .
Arguments anyexpr_ty / .
Arguments unwrap / .
Arguments invert_AppIdentOrLiteral_cps / .
Arguments invert_AppIdent_cps / .
Arguments mkapp_from_context / .
Arguments unmkapp_to_context / .
Arguments bind_for_each_lhs_of_arrow_data_cps / .
Arguments type.app_fold_for_each_lhs_of_arrow_ind / .
Arguments type.lift_bind_for_each_lhs_of_arrow_indT / .
Definition dorewrite
  := Eval cbn [dorewrite' dorewrite1 do_rewrite_ident eval_rewrite_rules dtree eval_decision_tree eta_ident_cps eta_option_ident_cps option_map List.app rewrite_rules nth_error bind_data_cps ident_beq_cps ident_beq_cps list_rect Option.bind swap_list set_nth update_nth lift_with_bindings app_binding_data type.try_transport_cps type.try_transport_cps' unwrap anyexpr_ty invert_AppIdentOrLiteral_cps mkapp_from_context unmkapp_to_context invert_AppIdent_cps bind_for_each_lhs_of_arrow_data_cps type.app_fold_for_each_lhs_of_arrow_ind type.lift_bind_for_each_lhs_of_arrow_indT] in @dorewrite'.
Arguments dorewrite {t} e.
Print dorewrite.
(* dorewrite =
fix dorewrite' (t : type) (e : expr t) {struct e} :
value t :=
  match e in (expr t0) return (value t0) with
  | #(idc)%expr =>
      match idc in (ident t1) return (value t1) with
      | O => 0%expr
      | S => fun x : expr Nat => (x.+1)%expr
      | Add =>
          fun x x0 : expr Nat =>
          match x with
          | 0%expr => x0
          | @App s _ #(S)%expr y =>
              match s as t2 return (expr t2 -> expr Nat) with
              | Nat =>
                  fun v : expr Nat =>
                  match x0 with
                  | 0%expr => (v.+1)%expr
                  | @App s0 _ #(S)%expr y0 =>
                      match s0 as t3 return (expr t3 -> expr Nat) with
                      | Nat => fun v0 : expr Nat => ((v + v0.+1).+1)%expr
                      | (s1 -> d1)%ctype =>
                          fun _ : expr (s1 -> d1) => (x + x0)%expr
                      end y0
                  | @App s0 _ (@App s1 _ #(Add)%expr x1) y0 =>
                      match s1 as t3 return (expr t3 -> expr Nat) with
                      | Nat =>
                          fun v0 : expr Nat =>
                          match s0 as t3 return (expr t3 -> expr Nat) with
                          | Nat =>
                              fun v1 : expr Nat => ((v + (v0 + v1)).+1)%expr
                          | (s2 -> d2)%ctype =>
                              fun _ : expr (s2 -> d2) => (x + x0)%expr
                          end y0
                      | (s2 -> d2)%ctype =>
                          fun _ : expr (s2 -> d2) =>
                          match s0 as t3 return (expr t3 -> expr Nat) with
                          | Nat => fun _ : expr Nat => (x + x0)%expr
                          | (s3 -> d3)%ctype =>
                              fun _ : expr (s3 -> d3) => (x + x0)%expr
                          end y0
                      end x1
                  | @App s0 _ (@App s1 _ 0%expr _) _ | @App s0 _
                    (@App s1 _ #(S)%expr _) _ | @App s0 _
                    (@App s1 _ (_ @ _)%expr _) _ | @App s0 _
                    (@App s1 _ ##(_)%expr _) _ => (x + x0)%expr
                  | @App s0 _ 0%expr _ | @App s0 _ #
                    (Add)%expr _ | @App s0 _ ##(_)%expr _ =>
                      (x + x0)%expr
                  | ##(n)%expr => ((v + ##(n)).+1)%expr
                  | _ => (x + x0)%expr
                  end
              | (s0 -> d0)%ctype => fun _ : expr (s0 -> d0) => (x + x0)%expr
              end y
          | @App s _ (@App s0 _ #(Add)%expr x1) y =>
              match s0 as t2 return (expr t2 -> expr Nat) with
              | Nat =>
                  fun v : expr Nat =>
                  match s as t2 return (expr t2 -> expr Nat) with
                  | Nat =>
                      fun v0 : expr Nat =>
                      match x0 with
                      | 0%expr => (v + v0)%expr
                      | @App s1 _ #(S)%expr y0 =>
                          match s1 as t3 return (expr t3 -> expr Nat) with
                          | Nat =>
                              fun v1 : expr Nat => ((v + v0 + v1).+1)%expr
                          | (s2 -> d2)%ctype =>
                              fun _ : expr (s2 -> d2) => (x + x0)%expr
                          end y0
                      | @App s1 _ (@App s2 _ #(Add)%expr x2) y0 =>
                          match s2 as t3 return (expr t3 -> expr Nat) with
                          | Nat =>
                              fun _ : expr Nat =>
                              match s1 as t3 return (expr t3 -> expr Nat) with
                              | Nat => fun _ : expr Nat => (x + x0)%expr
                              | (s3 -> d3)%ctype =>
                                  fun _ : expr (s3 -> d3) => (x + x0)%expr
                              end y0
                          | (s3 -> d3)%ctype =>
                              fun _ : expr (s3 -> d3) =>
                              match s1 as t3 return (expr t3 -> expr Nat) with
                              | Nat => fun _ : expr Nat => (x + x0)%expr
                              | (s4 -> d4)%ctype =>
                                  fun _ : expr (s4 -> d4) => (x + x0)%expr
                              end y0
                          end x2
                      | @App s1 _ (@App s2 _ 0%expr _) _ | @App s1 _
                        (@App s2 _ #(S)%expr _) _ | @App s1 _
                        (@App s2 _ (_ @ _)%expr _) _ | @App s1 _
                        (@App s2 _ ##(_)%expr _) _ =>
                          (x + x0)%expr
                      | @App s1 _ 0%expr _ | @App s1 _ #
                        (Add)%expr _ | @App s1 _ ##
                        (_)%expr _ => (x + x0)%expr
                      | _ => (x + x0)%expr
                      end
                  | (s1 -> d1)%ctype =>
                      fun _ : expr (s1 -> d1) => (x + x0)%expr
                  end y
              | (s1 -> d1)%ctype =>
                  fun _ : expr (s1 -> d1) =>
                  match s as t2 return (expr t2 -> expr Nat) with
                  | Nat => fun _ : expr Nat => (x + x0)%expr
                  | (s2 -> d2)%ctype =>
                      fun _ : expr (s2 -> d2) => (x + x0)%expr
                  end y
              end x1
          | @App s _ (@App s0 _ 0%expr _) _ | @App s _
            (@App s0 _ #(S)%expr _) _ | @App s _ (@App s0 _ (_ @ _)%expr _)
            _ | @App s _ (@App s0 _ ##(_)%expr _) _ =>
              (x + x0)%expr
          | @App s _ 0%expr _ | @App s _ #(Add)%expr _ | @App s _ ##
            (_)%expr _ => (x + x0)%expr
          | ##(n)%expr =>
              match x0 with
              | 0%expr => ##(n)%expr
              | @App s _ #(S)%expr y =>
                  match s as t2 return (expr t2 -> expr Nat) with
                  | Nat => fun v : expr Nat => ((##(n) + v).+1)%expr
                  | (s0 -> d0)%ctype =>
                      fun _ : expr (s0 -> d0) => (x + x0)%expr
                  end y
              | @App s _ (@App s0 _ #(Add)%expr x1) y =>
                  match s0 as t2 return (expr t2 -> expr Nat) with
                  | Nat =>
                      fun _ : expr Nat =>
                      match s as t2 return (expr t2 -> expr Nat) with
                      | Nat => fun _ : expr Nat => (x + x0)%expr
                      | (s1 -> d1)%ctype =>
                          fun _ : expr (s1 -> d1) => (x + x0)%expr
                      end y
                  | (s1 -> d1)%ctype =>
                      fun _ : expr (s1 -> d1) =>
                      match s as t2 return (expr t2 -> expr Nat) with
                      | Nat => fun _ : expr Nat => (x + x0)%expr
                      | (s2 -> d2)%ctype =>
                          fun _ : expr (s2 -> d2) => (x + x0)%expr
                      end y
                  end x1
              | @App s _ (@App s0 _ 0%expr _) _ | @App s _
                (@App s0 _ #(S)%expr _) _ | @App s _
                (@App s0 _ (_ @ _)%expr _) _ | @App s _
                (@App s0 _ ##(_)%expr _) _ => (x + x0)%expr
              | @App s _ 0%expr _ | @App s _ #(Add)%expr _ | @App s _
                ##(_)%expr _ => (x + x0)%expr
              | ##(n0)%expr => ##(n + n0)%expr
              | _ => (x + x0)%expr
              end
          | _ => (x + x0)%expr
          end
      end
  | @App s d f x =>
      match s as s0 return (expr (s0 -> d) -> expr s0 -> value d) with
      | Nat =>
          fun (f0 : expr (Nat -> d)) (x0 : expr Nat) =>
          dorewrite' (Nat -> d)%ctype f0 (dorewrite' Nat x0)
      | (s0 -> d0)%ctype =>
          fun (f0 : expr ((s0 -> d0) -> d)) (x0 : expr (s0 -> d0)) =>
          dorewrite' ((s0 -> d0) -> d)%ctype f0 x0
      end f x
  | ##(n)%expr => ##(n)%expr
  end
     : forall t : type, expr t -> value t

Argument t is implicit and maximally inserted
Argument scopes are [ctype_scope expr_scope]
*)
