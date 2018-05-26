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

Module type.
  Fixpoint base_interp (t : base_type) : Set
    := match t with
       | Nat => nat
       | Prod A B => base_interp A * base_interp B
       end%type.
  Fixpoint interp_gen (binterp : base_type -> Set) (t : type) : Set
    := match t with
       | Base t => binterp t
       | Arrow s d => binterp s -> interp_gen binterp d
       end.
  Definition interp : type -> Set := interp_gen base_interp.
  Fixpoint final_codomain (t : type) : base_type
    := match t with
       | Base t => t
       | Arrow s d => final_codomain d
       end.
  Fixpoint for_each_lhs_of_arrow (f : base_type -> Set) (t : type) : Set
    := match t with
       | Base _ => unit
       | Arrow s d => f s * for_each_lhs_of_arrow f d
       end.
  Inductive for_each_lhs_of_arrow_ind (f : base_type -> Set) : type -> Set :=
  | NoLHS {t} : for_each_lhs_of_arrow_ind f (Base t)
  | ArrowLHS {s d} (_ : f s) (_ : for_each_lhs_of_arrow_ind f d) : for_each_lhs_of_arrow_ind f (s -> d).
  Global Arguments NoLHS {_ _}.
  Global Arguments ArrowLHS {_ _ _} _ _.

  Definition hd_for_each_lhs_of_arrow_ind {f s d} (x : for_each_lhs_of_arrow_ind f (Arrow s d))
    : f s
    := match x with
       | ArrowLHS _ _ x xs => x
       end.

  Definition tl_for_each_lhs_of_arrow_ind {f s d} (x : for_each_lhs_of_arrow_ind f (Arrow s d))
    : for_each_lhs_of_arrow_ind f d
    := match x with
       | ArrowLHS _ _ x xs => xs
       end.

  Fixpoint for_each_lhs_of_arrow_of_ind {f : base_type -> Set} {t : type}
    : for_each_lhs_of_arrow_ind f t -> for_each_lhs_of_arrow f t
    := match t with
       | Base _ => fun _ => tt
       | Arrow s d
         => fun x
            => let '(x, xs) := (hd_for_each_lhs_of_arrow_ind x, tl_for_each_lhs_of_arrow_ind x) in
               (x, @for_each_lhs_of_arrow_of_ind f d xs)
       end.

  Global Coercion for_each_lhs_of_arrow_of_ind : for_each_lhs_of_arrow_ind >-> for_each_lhs_of_arrow.


  Fixpoint fold_for_each_lhs_of_arrow {f : base_type -> Set} (F : forall t, f t -> Type) {t}
    : for_each_lhs_of_arrow f t -> Type
    := match t return for_each_lhs_of_arrow f t -> Type with
       | Base _ => fun _ => unit
       | Arrow s d
         => fun '(x, xs)
            => F _ x * @fold_for_each_lhs_of_arrow f F d xs
       end%type.

  Fixpoint bind_for_each_lhs_of_arrowT {f : base_type -> Set} (F : forall t, f t -> Type -> Type) {t}
    : for_each_lhs_of_arrow f t -> Type -> Type
    := match t return for_each_lhs_of_arrow f t -> Type -> Type with
       | Base _ => fun _ T => T
       | Arrow s d
         => fun '(x, xs) T
            => F _ x (@bind_for_each_lhs_of_arrowT f F d xs T)
       end%type.

  Section fold_for_each_lhs_of_arrow.
    Context {f : base_type -> Set}
            (F : forall t, f t -> Type).
    Fixpoint fold_for_each_lhs_of_arrow_ind {t} (xs : for_each_lhs_of_arrow_ind f t) : Type
      := match xs return Type with
         | NoLHS _ => unit
         | ArrowLHS s d x xs
           => F _ x * @fold_for_each_lhs_of_arrow_ind d xs
         end.
  End fold_for_each_lhs_of_arrow.
  Section bind_for_each_lhs_of_arrow.
    Context {f : base_type -> Set}
            (F : forall t, f t -> Type -> Type)
            (T : Type).
    Fixpoint bind_for_each_lhs_of_arrow_indT {t} (xs : for_each_lhs_of_arrow_ind f t)
      : Type
      := match xs with
         | NoLHS _ => T
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
           | NoLHS _ => fun v _ => v
           | ArrowLHS s d x xs
             => fun G '(v, vs)
                => @app_fold_for_each_lhs_of_arrow_ind d xs (APP _ _ _ G v) vs
           end.
    End app.
  End bind_for_each_lhs_of_arrow.
  Section bind_for_each_lhs_of_arrow2.
    Context {f : base_type -> Set}
            (F : forall t, f t -> Type -> Type)
            {A B : Type}
            (G : A -> B)
            (lift_G : forall t ft A B, (A -> B) -> F t ft A -> F t ft B).
    Fixpoint lift_bind_for_each_lhs_of_arrow_indT
             {t} (xs : for_each_lhs_of_arrow_ind f t)
      : bind_for_each_lhs_of_arrow_indT F A xs -> bind_for_each_lhs_of_arrow_indT F B xs
      := match xs return bind_for_each_lhs_of_arrow_indT F A xs -> bind_for_each_lhs_of_arrow_indT F B xs with
         | NoLHS _ => G
         | ArrowLHS s d x xs
           => lift_G
                _ _ _ _
                (@lift_bind_for_each_lhs_of_arrow_indT d xs)
         end%type.
  End bind_for_each_lhs_of_arrow2.

  Fixpoint const_for_each_lhs_of_arrow {P : base_type -> Set} (v : forall t, P t) {t} : for_each_lhs_of_arrow P t
    := match t with
       | Base _ => tt
       | Arrow s d => (v s, @const_for_each_lhs_of_arrow P v d)
       end.

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
  Fixpoint try_transport_base (P : base_type -> Type) (t1 t2 : base_type)
    : P t1 -> option (P t2)
    := match t1, t2 with
       | Nat, Nat => fun v => Some v
       | Prod s d, Prod s' d'
         => fun v
            => (v' <- (try_transport_base
                         (fun s => P (Prod s _)) _ _ v);
                  try_transport_base
                    (fun d => P (Prod _ d)) _ _ v')
       | Nat, _
       | Prod _ _, _
         => fun _ => None
       end%option.

  Fixpoint try_transport (P : type -> Type) (t1 t2 : type)
    : P t1 -> option (P t2)
    := match t1, t2 with
       | Base t1, Base t2 => try_transport_base (fun t => P (Base t)) t1 t2
       | Arrow s d, Arrow s' d'
         => fun v
            => (v' <- (try_transport_base
                         (fun s => P (Arrow s _)) _ _ v);
                  try_transport
                    (fun d => P (Arrow _ d)) _ _ v')
       | Base _, _
       | Arrow _ _, _
         => fun _ => None
       end%option.
(*
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
*)
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
| Add : ident (Nat -> Nat -> Nat)
| PairNat : ident (Nat -> Nat -> Nat * Nat)
| FstNat : ident (Nat * Nat -> Nat)
| SndNat : ident (Nat * Nat -> Nat).

Fixpoint ident_beq_cps {T t t'} (X : ident t) (Y : ident t') (k : bool -> T) {struct X} : T
  := match X, Y with
     | O, O
     | S, S
     | Add, Add
     | PairNat, PairNat
     | FstNat, FstNat
     | SndNat, SndNat
       => k true
     | O, _
     | S, _
     | Add, _
     | PairNat, _
     | FstNat, _
     | SndNat, _
       => k false
     end.

Definition eta_option_ident_cps {T} (f : forall t, ident t -> option (T t))
  : option (forall t, ident t -> T t)
  := (fO <- f _ O;
        fS <- f _ S;
        fAdd <- f _ Add;
        fPairNat <- f _ PairNat;
        fFstNat <- f _ FstNat;
        fSndNat <- f _ SndNat;
        Some (fun _ c
              => match c with
                 | O => fO
                 | S => fS
                 | Add => fAdd
                 | PairNat => fPairNat
                 | FstNat => fFstNat
                 | SndNat => fSndNat
                 end))%option.

Definition eta_ident_cps {T t} (c : ident t) (f : forall t, ident t -> T t) : T t
  := Eval cbv [invert_Some Option.bind eta_option_ident_cps] in
      invert_Some (eta_option_ident_cps (fun _ c' => Some (f _ c'))) _ c.

Definition orb_ident (f : forall t, ident t -> bool) : bool
  := (f _ O || f _ S || f _ Add || f _ PairNat || f _ FstNat || f _ SndNat)%bool.

Inductive expr : type -> Set :=
| AppIdent {t} (idc : ident t) (args : type.for_each_lhs_of_arrow_ind expr t) : expr (type.final_codomain t)
| Literal (n : nat) : expr Nat.

Inductive pattern : Set :=
| Wildcard (t : option base_type)
| pLiteral
| pAppIdent {t} (idc : ident t) (args : type.for_each_lhs_of_arrow_ind (fun _ => pattern) t).

Inductive rawexpr : Set :=
| rAppIdent {t} (idc : ident t) (args : type.for_each_lhs_of_arrow_ind (fun _ => rawexpr) t) (alt : expr (type.final_codomain t))
| rLiteral (n : nat) (alt : expr Nat)
| rExpr {t : base_type} (e : expr t).

Definition type_of_rawexpr (e : rawexpr) : base_type
  := match e with
     | rAppIdent t idc args alt => type.final_codomain t
     | rLiteral n alt => Nat
     | rExpr t e => t
     end.
Definition expr_of_rawexpr (e : rawexpr) : expr (type_of_rawexpr e)
  := match e with
     | rAppIdent t idc args alt => alt
     | rLiteral n alt => alt
     | rExpr t e => e
     end.

Delimit Scope expr_scope with expr.
Bind Scope expr_scope with expr.
(*Notation "# idc" := (Ident idc) : expr_scope.*)
Notation "## n" := (Literal n) : expr_scope.
(*Infix "@" := App : expr_scope.*)
Notation "0" := (AppIdent O []%for_each_lhs_of_arrow)%expr : expr_scope.
Notation "n '.+1'" := (AppIdent S (type.ArrowLHS n type.NoLHS))%expr (at level 10, format "n '.+1'") : expr_scope.
Notation "x + y" := (AppIdent Add (type.ArrowLHS x (type.ArrowLHS y type.NoLHS)))%expr : expr_scope.

Delimit Scope pattern_scope with pattern.
Bind Scope pattern_scope with pattern.
Notation "#?" := pLiteral : pattern_scope.
Notation "??" := (Wildcard None) : pattern_scope.
Notation "??ℕ" := (Wildcard (Some Nat)) : pattern_scope.
Notation "??ℕℕ" := (Wildcard (Some (Prod Nat Nat))) : pattern_scope.
Notation "0" := (pAppIdent O []%for_each_lhs_of_arrow)%pattern : pattern_scope.
Notation "n '.+1'" := (pAppIdent S (type.ArrowLHS n type.NoLHS))%pattern (at level 10, format "n '.+1'") : pattern_scope.
Notation "x + y" := (pAppIdent Add (type.ArrowLHS x (type.ArrowLHS y type.NoLHS)))%pattern : pattern_scope.

Record anyexpr := wrap { anyexpr_ty : base_type ; unwrap :> expr anyexpr_ty }.
Arguments wrap {_} _.

Fixpoint mkapp_from_context_helper (t : type) (ctx : list rawexpr)
  : option (type.for_each_lhs_of_arrow_ind (fun _ => rawexpr) t * list rawexpr)
  := match t, ctx return option (type.for_each_lhs_of_arrow_ind (fun _ => rawexpr) t * list rawexpr) with
     | Base _, ctx' => Some ([], ctx')
     | Arrow s d, x :: ctx'
       => match mkapp_from_context_helper d ctx' with
          | Some (args, ctx'')
            => Some (type.ArrowLHS x args, ctx'')
          | None => None
          end
     | Arrow _ _, nil => None
     end%for_each_lhs_of_arrow%core%expr.

Definition mkapp_from_context {t} (idc : ident t) (ctx : list rawexpr) (alt : expr (type.final_codomain t))
  : option (list rawexpr)
  := option_map
       (fun '(args, ctx') => rAppIdent idc args alt :: ctx')
       (mkapp_from_context_helper t ctx).

Fixpoint unmkapp_to_context {P : base_type -> Set} {Q}
           (wrap : forall t : base_type, P t -> Q)
           (t : type)
           (args : type.for_each_lhs_of_arrow P t)
           (ctx : list Q)
           {struct t}
  : list Q
  := match t return type.for_each_lhs_of_arrow P t -> list Q with
     | Base _ => fun _ => ctx
     | Arrow s d
       => fun '(x, args) => wrap _ x :: @unmkapp_to_context P Q wrap d args ctx
     end args.

Definition invert_AppIdent_cps {T t} (e : expr t) (args : type.for_each_lhs_of_arrow expr t) : (option { t' : _ & ident t' * type.for_each_lhs_of_arrow expr t' }%type -> T) -> T
  := match e in expr t return type.for_each_lhs_of_arrow expr t -> (option _ -> T) -> T with
     | AppIdent t idc args
       => fun _ k
          => k (Some (existT (fun t' => ident t' * type.for_each_lhs_of_arrow expr t')%type
                             t (idc, type.for_each_lhs_of_arrow_of_ind args)))
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
Section invert_AppIdentOrLiteral_cps.
  Context (do_literal : bool)
          (do_ident : forall t, ident t -> bool)
          {t T}
          (e : expr (Base t)) (args : type.for_each_lhs_of_arrow_ind expr t)
          (T0P := fun t' => (ident t' * type.for_each_lhs_of_arrow expr t' * expr (type.final_codomain t'))%type)
          (T0 := sigT T0P)
          (k : option (T0 + nat * expr Nat) -> T).

  Definition invert_AppIdentOrLiteral_cps
    : T
    := Eval cbv [orb_ident] in
        if (orb_ident do_ident || do_literal)%bool
        then match e with
             | Literal n
               => if do_literal
                  then match type.try_transport _ _ _ e with
                       | Some e' => k (Some (inr (n, e')))
                       | None => k None
                       end
                  else k None
             | AppIdent _ idc args
               => if orb_ident do_ident
                  then eta_ident_cps
                         (T:=fun t => type.for_each_lhs_of_arrow_ind expr t -> T)
                         idc
                         (fun _ idc args
                          => if do_ident _ idc
                             then match type.try_transport _ _ _ e with
                                  | Some e' => k (Some (inl (existT T0P _ (idc, type.for_each_lhs_of_arrow_of_ind args, e'))))
                                  | None => k None
                                  end
                             else k None)
                         args
                  else k None
             end
        else k None.
End invert_AppIdentOrLiteral_cps.

Definition hlist {A} (f : A -> Set) (ls : list A)
  := fold_right
       (fun a b : Set => prod a b)
       unit
       (map f ls).

Fixpoint binding_dataT (p : pattern)
  := match p return Type with
     | Wildcard None => anyexpr
     | Wildcard (Some t) => expr t
     | pLiteral => nat
     | pAppIdent t idc args => type.fold_for_each_lhs_of_arrow_ind (fun _ => binding_dataT) args
     end%type.

Section bind_data_cps_helper.
  Context {T} {P : base_type -> Set}
          (bind_data_cps : forall {t : base_type} (e : P t) (p : pattern),
              (option (binding_dataT p) -> T) -> T).

  Fixpoint bind_for_each_lhs_of_arrow_data_cps
           {t}
           (pargs : type.for_each_lhs_of_arrow_ind (fun _ => pattern) t)
    : forall (args : type.for_each_lhs_of_arrow P t)
             (k : option
                    (type.fold_for_each_lhs_of_arrow_ind (fun _ => binding_dataT)
                                                         pargs) -> T),
      T
    := match pargs in type.for_each_lhs_of_arrow_ind _ t
             return (forall (args : type.for_each_lhs_of_arrow P t)
                            (k : option
                                   (type.fold_for_each_lhs_of_arrow_ind (fun _ => binding_dataT)
                                                                        pargs) -> T),
                        T)
       with
       | type.NoLHS _ => fun tt k => k (Some tt)
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

Fixpoint bind_data_cps {T} (e : rawexpr) (p : pattern) {struct p}
  : (option (binding_dataT p) -> T) -> T
  := match p return (option (binding_dataT p) -> T) -> T with
     | Wildcard None
       => fun k => k (Some (wrap (expr_of_rawexpr e)))
     | Wildcard (Some _)
       => fun k => type.try_transport_cps _ _ _ (expr_of_rawexpr e) k
     | pLiteral
       => fun k
          => match e with
             | rLiteral n alt => k (Some n)
             | _ => k None
             end
     | pAppIdent pt pidc pargs
       => fun k
          => match e with
             | rAppIdent t idc args _
               => ident_beq_cps
                    pidc idc
                    (fun b
                     => if b
                        then type.try_transport_cps
                               (type.for_each_lhs_of_arrow_ind _) _ _ args
                               (fun args'
                                => match args' with
                                   | Some args'
                                     => bind_for_each_lhs_of_arrow_data_cps
                                          (fun _ => @bind_data_cps T)
                                          pargs args' k
                                   | None => k None
                                   end)
                        else k None)
             | _ => k None
             end
     end.
(*
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
*)
Inductive decision_tree :=
| TryLeaf (k : nat) (onfailure : decision_tree)
| Failure
| Switch (icases : forall t, ident t -> option decision_tree)
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
     | Switch icases lit_case default_case
       => let do_literal := match lit_case with Some _ => true | None => false end in
          let default _ := @eval_decision_tree T ctx default_case cont in
          match ctx with
          | nil => cont None ctx None
          | rLiteral n alt :: ctx'
            => match lit_case with
               | Some lit_case
                 => @eval_decision_tree
                      T ctx' lit_case
                      (fun k ctx''
                       => cont k (rLiteral n alt :: ctx''))
               | None => default tt
               end
          | rAppIdent t idc args alt :: ctx'
            => match icases _ idc with
               | Some icase
                 => @eval_decision_tree
                      T (unmkapp_to_context (fun _ (x:rawexpr) => x) t args ctx') icase
                      (fun k ctx''
                       => match mkapp_from_context idc ctx'' alt with
                          | Some ctx'''
                            => cont k ctx'''
                          | None => cont None ctx
                          end)
               | None => default tt
               end
          | rExpr t ctx0 :: ctx'
            => invert_AppIdentOrLiteral_cps
                 do_literal
                 (fun _ idc => match icases _ idc with Some _ => true | None => false end)
                 ctx0 (*tt*)
                 (fun ctx0'
                  => match ctx0' with
                     | Some (inr (n, ctx0'')) (* Literal *)
                       => match lit_case with
                          | Some lit_case
                            => @eval_decision_tree
                                 T ctx' lit_case
                                 (fun k ctx''
                                  => cont k (rLiteral n ctx0'' :: ctx''))
                          | None => default tt
                          end
                     | Some (inl (existT _ (idc, args, ctx0'')))
                       => match icases _ idc with
                          | Some icase
                            => @eval_decision_tree
                                 T (unmkapp_to_context (@rExpr) _ args ctx') icase
                                 (fun k ctx''
                                  => match mkapp_from_context idc ctx'' ctx0'' with
                                     | Some ctx'''
                                       => cont k ctx'''
                                     | None => cont None ctx
                                     end)
                          | None => default tt
                          end
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
           {t}
           (d : decision_tree)
           (rew : list { p : pattern & { t' : type & binding_dataT p -> option (expr t') } })
           (e : expr (Base t))
  : expr (Base t)
  := eval_decision_tree
       (rExpr e::nil) d
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
                       | Wildcard _ => None
                       | _ => Some n
                       end)
       (enumerate p).

Definition filter_pattern_wildcard (p : nat * list pattern) : nat * list pattern
  := (fst p, filter (fun p => match p with
                              | Wildcard _ => true
                              | _ => false
                              end)
                    (snd p)).

Definition contains_pattern_literal (p : list (nat * list pattern)) : bool
  := match find (fun '(n, p) => match p with
                                | pLiteral::_ => true
                                | _ => false
                                end)
                p
     with
     | Some _ => true
     | None => false
     end.

Definition contains_pattern_ident {t} (idc : ident t) (p : list (nat * list pattern)) : bool
  := match find (fun '(n, p) => match p with
                                | pAppIdent t' idc' _::_ => ident_beq_cps idc' idc (fun b => b)
                                | _ => false
                                end)
                p
     with
     | Some _ => true
     | None => false
     end.

Definition refine_pattern_literal (p : nat * list pattern) : option (nat * list pattern)
  := match p with
     | (n, Wildcard _::ps)
     | (n, pLiteral::ps)
       => Some (n, ps)
     | (_, pAppIdent _ _ _::_)
     | (_, nil)
       => None
     end.

Definition refine_pattern_app_ident {t} (idc : ident t) (p : nat * list pattern) : option (nat * list pattern)
  := match p with
     | (n, Wildcard _::ps)
       => let p' := unmkapp_to_context (fun _ (p : pattern) => p) t (type.const_for_each_lhs_of_arrow (fun t => Wildcard (Some t))) ps in
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
                           let p' := unmkapp_to_context (fun _ (p : pattern) => p) t pargs' ps in
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
            => default_case <- compile_rewrites (List.map filter_pattern_wildcard pattern_matrix);
                 lit_case <- (if contains_pattern_literal pattern_matrix
                              then option_map Some (compile_rewrites (omap refine_pattern_literal pattern_matrix))
                              else Some None);
                 icases
                   <- (eta_option_ident_cps
                         (fun _ idc => if contains_pattern_ident idc pattern_matrix
                                       then option_map Some (compile_rewrites (omap (refine_pattern_app_ident idc) pattern_matrix))
                                       else Some None));
                 Some (Switch icases lit_case default_case)
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
     | Wildcard (Some t) => expr t -> T
     | Wildcard None => forall t, expr (Base t) -> T
     | pLiteral => nat -> T
     | pAppIdent _ idc args
       => type.bind_for_each_lhs_of_arrow_indT (fun _ => with_bindingsT) T args
     end.

Fixpoint lift_with_bindings {p A B} (F : A -> B) {struct p} : with_bindingsT p A -> with_bindingsT p B
  := match p return with_bindingsT p A -> with_bindingsT p B with
     | Wildcard (Some _) => fun f e => F (f e)
     | Wildcard None => fun f _ e => F (f _ e)
     | pLiteral => fun f e => F (f e)
     | pAppIdent t idc args
       => type.lift_bind_for_each_lhs_of_arrow_indT
            _ F (fun _ => @lift_with_bindings) args
     end.

Fixpoint app_binding_data {T p} : forall (f : with_bindingsT p T) (v : binding_dataT p), T
  := match p return forall (f : with_bindingsT p T) (v : binding_dataT p), T with
     | Wildcard (Some _)
     | pLiteral
       => fun f => f
     | Wildcard None
       => fun f v => f _ (unwrap v)
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
  := [make_rewrite (0 + ??ℕ) (fun x => x);
        make_rewrite (??ℕ + 0) (fun x => x);
        make_rewrite (#? + #?) (fun x y => ##(x + y));
        make_rewrite (??ℕ.+1 + ??ℕ.+1) (fun x y => (x+y).+1.+1);
        make_rewrite (??ℕ.+1 + ??ℕ) (fun x y => (x+y).+1);
        make_rewrite (??ℕ + ??ℕ.+1) (fun x y => (x+y).+1);
        make_rewrite (pAppIdent FstNat [pAppIdent PairNat [??ℕ; ??ℕ] ])
                     (fun x y => x);
        make_rewrite (pAppIdent SndNat [pAppIdent PairNat [??ℕ; ??ℕ] ])
                     (fun x y => y)
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

Fixpoint dorewrite' {t} (e : expr t) : value t
  := match e in expr t return value t with
     | AppIdent t idc args
       => eta_ident_cps
            idc
            (fun _ idc' args' => dorewrite1 (AppIdent idc' args'))
            args
     | Literal _ as e => e
     end.

Arguments bind_data_cps / .
Arguments dorewrite1 / .
Arguments dorewrite' / .
Arguments rewrite_rules / .
(*Arguments domatch / .*)
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
Arguments anyexpr_ty / .
Arguments unwrap / .
Arguments invert_AppIdentOrLiteral_cps / .
Arguments invert_AppIdent_cps / .
Arguments mkapp_from_context / .
Arguments unmkapp_to_context / .
Arguments bind_for_each_lhs_of_arrow_data_cps / .
Arguments type.app_fold_for_each_lhs_of_arrow_ind / .
Arguments type.lift_bind_for_each_lhs_of_arrow_indT / .
Arguments type.for_each_lhs_of_arrow_of_ind / .
Arguments type_of_rawexpr / .
Arguments expr_of_rawexpr / .
Arguments mkapp_from_context_helper / .
Definition dorewrite''
  := Eval cbv [dorewrite' dorewrite1 eval_rewrite_rules dtree eval_decision_tree eta_ident_cps eta_option_ident_cps option_map List.app rewrite_rules nth_error bind_data_cps ident_beq_cps ident_beq_cps list_rect Option.bind swap_list set_nth update_nth lift_with_bindings app_binding_data type.try_transport_cps type.try_transport_base_cps unwrap anyexpr_ty invert_AppIdentOrLiteral_cps mkapp_from_context unmkapp_to_context invert_AppIdent_cps bind_for_each_lhs_of_arrow_data_cps type.app_fold_for_each_lhs_of_arrow_ind type.lift_bind_for_each_lhs_of_arrow_indT type.for_each_lhs_of_arrow_of_ind type_of_rawexpr expr_of_rawexpr mkapp_from_context_helper type.try_transport Option.bind orb] in @dorewrite'.
Arguments dorewrite'' / .
Definition dorewrite
  := Eval cbn [dorewrite'' type.final_codomain type.try_transport_base Option.bind type.hd_for_each_lhs_of_arrow_ind type.tl_for_each_lhs_of_arrow_ind] in @dorewrite''.
Arguments dorewrite {t} e.
Print dorewrite.
(*dorewrite =
fix dorewrite' (t : type) (e : expr t) {struct t} :
value t :=
  match e in (expr t0) return (value t0) with
  | @AppIdent _ idc args =>
      match
        idc in (ident t1)
        return
          (type.for_each_lhs_of_arrow_ind (fun x : base_type => expr x) t1 ->
           expr (type.final_codomain t1))
      with
      | O =>
          fun
            args' : type.for_each_lhs_of_arrow_ind
                      (fun x : base_type => expr x) Nat =>
          AppIdent O args'
      | S =>
          fun
            args' : type.for_each_lhs_of_arrow_ind
                      (fun x : base_type => expr x)
                      (Nat -> Nat) => AppIdent S args'
      | Add =>
          fun
            args' : type.for_each_lhs_of_arrow_ind
                      (fun x : base_type => expr x)
                      (Nat -> Nat -> Nat) =>
          match
            type.hd_for_each_lhs_of_arrow_ind args' in (expr t1)
            return
              match t1 with
              | Base _ => expr Nat
              | (_ -> _)%ctype => IDProp
              end
          with
          | @AppIdent _ idc0 args0 =>
              match
                idc0 in (ident t2)
                return
                  (type.for_each_lhs_of_arrow_ind
                     (fun x : base_type => expr x) t2 ->
                   expr Nat)
              with
              | O =>
                  fun
                    _ : type.for_each_lhs_of_arrow_ind
                          (fun x : base_type => expr x) Nat =>
                  type.hd_for_each_lhs_of_arrow_ind
                    (type.tl_for_each_lhs_of_arrow_ind args')
              | S =>
                  fun
                    args1 : type.for_each_lhs_of_arrow_ind
                              (fun x : base_type => expr x)
                              (Nat -> Nat) =>
                  match
                    type.hd_for_each_lhs_of_arrow_ind
                      (type.tl_for_each_lhs_of_arrow_ind args') in
                    (expr t2)
                    return
                      match t2 with
                      | Base _ => expr Nat
                      | (_ -> _)%ctype => IDProp
                      end
                  with
                  | @AppIdent _ idc1 args2 =>
                      match
                        idc1 in (ident t3)
                        return
                          (type.for_each_lhs_of_arrow_ind
                             (fun x : base_type => expr x) t3 ->
                           expr Nat)
                      with
                      | O =>
                          fun
                            _ : type.for_each_lhs_of_arrow_ind
                                  (fun x : base_type => expr x) Nat =>
                          type.hd_for_each_lhs_of_arrow_ind args'
                      | S =>
                          fun
                            args3 : type.for_each_lhs_of_arrow_ind
                                      (fun x : base_type => expr x)
                                      (Nat -> Nat) =>
                          (((type.hd_for_each_lhs_of_arrow_ind args1 +
                             type.hd_for_each_lhs_of_arrow_ind args3).+1).+1)%expr
                      | Add =>
                          fun
                            _ : type.for_each_lhs_of_arrow_ind
                                  (fun x : base_type => expr x)
                                  (Nat -> Nat -> Nat) =>
                          AppIdent Add args'
                      | PairNat =>
                          fun
                            _ : type.for_each_lhs_of_arrow_ind
                                  (fun x : base_type => expr x)
                                  (Nat -> Nat -> Nat * Nat) =>
                          AppIdent Add args'
                      | _ =>
                          fun
                            _ : type.for_each_lhs_of_arrow_ind
                                  (fun x : base_type => expr x)
                                  (Nat * Nat -> Nat) =>
                          AppIdent Add args'
                      end args2
                  | ##(_)%expr => AppIdent Add args'
                  end
              | Add =>
                  fun
                    _ : type.for_each_lhs_of_arrow_ind
                          (fun x : base_type => expr x)
                          (Nat -> Nat -> Nat) => AppIdent Add args'
              | PairNat =>
                  fun
                    _ : type.for_each_lhs_of_arrow_ind
                          (fun x : base_type => expr x)
                          (Nat -> Nat -> Nat * Nat) =>
                  AppIdent Add args'
              | _ =>
                  fun
                    _ : type.for_each_lhs_of_arrow_ind
                          (fun x : base_type => expr x)
                          (Nat * Nat -> Nat) => AppIdent Add args'
              end args0
          | ##(n)%expr =>
              match
                type.hd_for_each_lhs_of_arrow_ind
                  (type.tl_for_each_lhs_of_arrow_ind args') in
                (expr t1)
                return
                  match t1 with
                  | Base _ => expr Nat
                  | (_ -> _)%ctype => IDProp
                  end
              with
              | @AppIdent _ idc0 args0 =>
                  match
                    idc0 in (ident t2)
                    return
                      (type.for_each_lhs_of_arrow_ind
                         (fun x : base_type => expr x) t2 ->
                       expr Nat)
                  with
                  | O =>
                      fun
                        _ : type.for_each_lhs_of_arrow_ind
                              (fun x : base_type => expr x) Nat =>
                      type.hd_for_each_lhs_of_arrow_ind args'
                  | S =>
                      fun
                        args1 : type.for_each_lhs_of_arrow_ind
                                  (fun x : base_type => expr x)
                                  (Nat -> Nat) =>
                      ((type.hd_for_each_lhs_of_arrow_ind args' +
                        type.hd_for_each_lhs_of_arrow_ind args1).+1)%expr
                  | Add =>
                      fun
                        _ : type.for_each_lhs_of_arrow_ind
                              (fun x : base_type => expr x)
                              (Nat -> Nat -> Nat) =>
                      AppIdent Add args'
                  | PairNat =>
                      fun
                        _ : type.for_each_lhs_of_arrow_ind
                              (fun x : base_type => expr x)
                              (Nat -> Nat -> Nat * Nat) =>
                      AppIdent Add args'
                  | _ =>
                      fun
                        _ : type.for_each_lhs_of_arrow_ind
                              (fun x : base_type => expr x)
                              (Nat * Nat -> Nat) =>
                      AppIdent Add args'
                  end args0
              | ##(n0)%expr => ##(n + n0)%expr
              end
          end
      | PairNat =>
          fun
            args' : type.for_each_lhs_of_arrow_ind
                      (fun x : base_type => expr x)
                      (Nat -> Nat -> Nat * Nat) =>
          AppIdent PairNat args'
      | FstNat =>
          fun
            args' : type.for_each_lhs_of_arrow_ind
                      (fun x : base_type => expr x)
                      (Nat * Nat -> Nat) =>
          match
            type.hd_for_each_lhs_of_arrow_ind args' in (expr t1)
            return
              match t1 with
              | Base _ => expr Nat
              | (_ -> _)%ctype => IDProp
              end
          with
          | @AppIdent _ idc0 args0 =>
              match
                idc0 in (ident t2)
                return
                  (type.for_each_lhs_of_arrow_ind
                     (fun x : base_type => expr x) t2 ->
                   expr Nat)
              with
              | O =>
                  fun
                    _ : type.for_each_lhs_of_arrow_ind
                          (fun x : base_type => expr x) Nat =>
                  AppIdent FstNat args'
              | S =>
                  fun
                    _ : type.for_each_lhs_of_arrow_ind
                          (fun x : base_type => expr x)
                          (Nat -> Nat) => AppIdent FstNat args'
              | Add =>
                  fun
                    _ : type.for_each_lhs_of_arrow_ind
                          (fun x : base_type => expr x)
                          (Nat -> Nat -> Nat) => AppIdent FstNat args'
              | PairNat =>
                  fun
                    args1 : type.for_each_lhs_of_arrow_ind
                              (fun x : base_type => expr x)
                              (Nat -> Nat -> Nat * Nat) =>
                  type.hd_for_each_lhs_of_arrow_ind args1
              | _ =>
                  fun
                    _ : type.for_each_lhs_of_arrow_ind
                          (fun x : base_type => expr x)
                          (Nat * Nat -> Nat) => AppIdent FstNat args'
              end args0
          | ##(_)%expr => AppIdent FstNat args'
          end
      | SndNat =>
          fun
            args' : type.for_each_lhs_of_arrow_ind
                      (fun x : base_type => expr x)
                      (Nat * Nat -> Nat) =>
          match
            type.hd_for_each_lhs_of_arrow_ind args' in (expr t1)
            return
              match t1 with
              | Base _ => expr Nat
              | (_ -> _)%ctype => IDProp
              end
          with
          | @AppIdent _ idc0 args0 =>
              match
                idc0 in (ident t2)
                return
                  (type.for_each_lhs_of_arrow_ind
                     (fun x : base_type => expr x) t2 ->
                   expr Nat)
              with
              | O =>
                  fun
                    _ : type.for_each_lhs_of_arrow_ind
                          (fun x : base_type => expr x) Nat =>
                  AppIdent SndNat args'
              | S =>
                  fun
                    _ : type.for_each_lhs_of_arrow_ind
                          (fun x : base_type => expr x)
                          (Nat -> Nat) => AppIdent SndNat args'
              | Add =>
                  fun
                    _ : type.for_each_lhs_of_arrow_ind
                          (fun x : base_type => expr x)
                          (Nat -> Nat -> Nat) => AppIdent SndNat args'
              | PairNat =>
                  fun
                    args1 : type.for_each_lhs_of_arrow_ind
                              (fun x : base_type => expr x)
                              (Nat -> Nat -> Nat * Nat) =>
                  type.hd_for_each_lhs_of_arrow_ind
                    (type.tl_for_each_lhs_of_arrow_ind args1)
              | _ =>
                  fun
                    _ : type.for_each_lhs_of_arrow_ind
                          (fun x : base_type => expr x)
                          (Nat * Nat -> Nat) => AppIdent SndNat args'
              end args0
          | ##(_)%expr => AppIdent SndNat args'
          end
      end args
  | ##(n)%expr => ##(n)%expr
  end
     : forall t : type, expr t -> value t

Argument t is implicit and maximally inserted
Argument scopes are [ctype_scope expr_scope]
*)
