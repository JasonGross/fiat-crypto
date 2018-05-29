Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.LetIn.
Import ListNotations.

Set Boolean Equality Schemes.
Inductive base_type := Nat | Prod (A B : base_type) | List (A : base_type).
Inductive type := Base (t : base_type) | Arrow (s : type) (d : type).
Coercion Base : base_type >-> type.
Bind Scope ctype_scope with type.
Bind Scope ctype_scope with base_type.
Delimit Scope ctype_scope with ctype.
Infix "->" := Arrow : ctype_scope.
Infix "*" := Prod : ctype_scope.

About fold_right.
Inductive ident : type -> Type :=
| O : ident Nat
| S : ident (Nat -> Nat)
| Add : ident (Nat -> Nat -> Nat)
| Pair {A B : base_type} : ident (A -> B -> A * B)
| Fst {A B} : ident (A * B -> A)
| Snd {A B} : ident (A * B -> B)
| Nil {A} : ident (List A)
| Cons {A : base_type} : ident (A -> List A -> List A)
| ListMap {A B : base_type} : ident ((A -> B) -> List A -> List B)
| ListApp {A} : ident (List A -> List A -> List A)
| ListFlatMap {A B : base_type} : ident ((A -> List B) -> List A -> List B)
| ListRect {A : base_type} {P : base_type} : ident (P -> (A -> List A -> P -> P) -> List A -> P)
| ListFoldRight {A : base_type} {B : base_type} : ident ((B -> A -> A) -> A -> List B -> A).

Show Match ident.
(*
<<<
#!/usr/bin/env python2

show_match_ident = r"""match # with
 | O =>
 | S =>
 | Add =>
 | Pair A B =>
 | Fst A B =>
 | Snd A B =>
 | Nil A =>
 | Cons A =>
 | ListMap A B =>
 | ListApp A =>
 | ListFlatMap A B =>
 | ListRect A P =>
 | ListFoldRight A B =>
 end

"""
ctors = [i.strip('|=> ').split(' ') for i in show_match_ident.split('\n') if i.strip().startswith('|')]
pctors = ['p' + i[0] for i in ctors]
print(r"""Inductive pident : Type :=
| %s.
""" % '\n| '.join(pctors))
print(r"""Definition pident_ident_beq {t} (X : pident) (Y : ident t) : bool
  := match X, Y with
     | %s
       => true
     | %s
       => false
     end.
""" % ('\n     | '.join(pctor + ', ' + ' '.join([ctor[0]] + ['_'] * (len(ctor)-1))
                        for pctor, ctor in zip(pctors, ctors)),
       '\n     | '.join(pctor + ', _' for pctor in pctors)))
print(r"""Definition eta_ident_cps {T t} (idc : ident t)
           (f : forall t, ident t -> T t)
  : T t
  := match idc with
     | %s
     end.
""" % ('\n     | '.join(' '.join(ctor) + ' => f _ '
                        + (('%s' if len(ctor) == 1 else '(@%s)')
                           % ' '.join(ctor))
                        for ctor in ctors)))
print(r"""Definition eta_option_pident_cps {T} (f : pident -> option T)
  : option (pident -> T)
  := (%s;
      Some (fun c
            => match c with
               | %s
               end))%%option.
""" % (';\n      '.join('f' + ctor[0] + ' <- f p' + ctor[0] for ctor in ctors),
       '\n               | '.join('p' + ctor[0] + ' => f' + ctor[0] for ctor in ctors)))
print(r"""Definition pident_of_ident {t} (idc : ident t) : pident
  := match idc with
     | %s
     end.
""" % ('\n     | '.join(' '.join(ctor) + ' => ' + pctor for ctor, pctor in zip(ctors, pctors))))
print(r"""Definition orb_pident (f : pident -> bool) : bool
  := (%s)%%bool.
""" % ' || '.join('f ' + pctor for pctor in pctors))
>>>
*)
Inductive pident : Type :=
| pO
| pS
| pAdd
| pPair
| pFst
| pSnd
| pNil
| pCons
| pListMap
| pListApp
| pListFlatMap
| pListRect
| pListFoldRight.

Definition pident_ident_beq {t} (X : pident) (Y : ident t) : bool
  := match X, Y with
     | pO, O
     | pS, S
     | pAdd, Add
     | pPair, Pair _ _
     | pFst, Fst _ _
     | pSnd, Snd _ _
     | pNil, Nil _
     | pCons, Cons _
     | pListMap, ListMap _ _
     | pListApp, ListApp _
     | pListFlatMap, ListFlatMap _ _
     | pListRect, ListRect _ _
     | pListFoldRight, ListFoldRight _ _
       => true
     | pO, _
     | pS, _
     | pAdd, _
     | pPair, _
     | pFst, _
     | pSnd, _
     | pNil, _
     | pCons, _
     | pListMap, _
     | pListApp, _
     | pListFlatMap, _
     | pListRect, _
     | pListFoldRight, _
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
     | Nil A => f _ (@Nil A)
     | Cons A => f _ (@Cons A)
     | ListMap A B => f _ (@ListMap A B)
     | ListApp A => f _ (@ListApp A)
     | ListFlatMap A B => f _ (@ListFlatMap A B)
     | ListRect A P => f _ (@ListRect A P)
     | ListFoldRight A B => f _ (@ListFoldRight A B)
     end.

Definition eta_option_pident_cps {T} (f : pident -> option T)
  : option (pident -> T)
  := (fO <- f pO;
      fS <- f pS;
      fAdd <- f pAdd;
      fPair <- f pPair;
      fFst <- f pFst;
      fSnd <- f pSnd;
      fNil <- f pNil;
      fCons <- f pCons;
      fListMap <- f pListMap;
      fListApp <- f pListApp;
      fListFlatMap <- f pListFlatMap;
      fListRect <- f pListRect;
      fListFoldRight <- f pListFoldRight;
      Some (fun c
            => match c with
               | pO => fO
               | pS => fS
               | pAdd => fAdd
               | pPair => fPair
               | pFst => fFst
               | pSnd => fSnd
               | pNil => fNil
               | pCons => fCons
               | pListMap => fListMap
               | pListApp => fListApp
               | pListFlatMap => fListFlatMap
               | pListRect => fListRect
               | pListFoldRight => fListFoldRight
               end))%option.

Definition pident_of_ident {t} (idc : ident t) : pident
  := match idc with
     | O => pO
     | S => pS
     | Add => pAdd
     | Pair A B => pPair
     | Fst A B => pFst
     | Snd A B => pSnd
     | Nil A => pNil
     | Cons A => pCons
     | ListMap A B => pListMap
     | ListApp A => pListApp
     | ListFlatMap A B => pListFlatMap
     | ListRect A P => pListRect
     | ListFoldRight A B => pListFoldRight
     end.

Definition orb_pident (f : pident -> bool) : bool
  := (f pO || f pS || f pAdd || f pPair || f pFst || f pSnd || f pNil || f pCons || f pListMap || f pListApp || f pListFlatMap || f pListRect || f pListFoldRight)%bool.
(*===*)

Definition or_opt_pident {T} (f : pident -> option T) : bool
  := orb_pident (fun p => match f p with Some _ => true | None => false end).

Inductive expr {var : type -> Type} : type -> Type :=
| Var {t} (v : var t) : expr t
| Abs {s d} (f : var s -> expr d) : expr (s -> d)
| Ident {t} (idc : ident t) : expr t
| App {s d} (f : expr (s -> d)) (x : expr s) : expr d
| Literal (n : nat) : expr Nat.

Inductive pbase_type := pbAny | pNat | pProd (A B : pbase_type) | pList (A : pbase_type).
Definition option_type := option type.
Coercion Some_t (t : type) : option_type := Some t.
Inductive ptype := pAny | pBase (t : pbase_type) | pArrow (s : option_type) (d : ptype).
Coercion pBase : pbase_type >-> ptype.
Bind Scope ptype_scope with ptype.
Bind Scope pbtype_scope with pbase_type.
Bind Scope ctype_scope with option_type.
Delimit Scope ptype_scope with ptype.
Delimit Scope pbtype_scope with pbtype.
Infix "->" := pArrow : ptype_scope.
Infix "*" := pProd : pbtype_scope.
Infix "*" := pProd : ptype_scope.
Notation "'??'" := pbAny : pbtype_scope.
Notation "'??'" := pAny : ptype_scope.
Local Set Warnings Append "-notation-overridden".
Notation "'??'" := (@None type) : ctype_scope.
Notation "'??'" := (@None base_type) : ctype_scope.
Notation "'??'" := None (only parsing) : ctype_scope.

Inductive pattern : Type :=
| Wildcardv (t : ptype)
| Wildcarde (t : option type)
| pIdent (idc : pident)
| pApp (f x : pattern)
| pLiteral.

Delimit Scope expr_scope with expr.
Bind Scope expr_scope with expr.
Notation "# idc" := (Ident idc) : expr_scope.
Notation "## n" := (Literal n) : expr_scope.
Infix "@" := App : expr_scope.
Notation "\ x .. y , f" := (Abs (fun x => .. (Abs (fun y => f%expr)) .. )) : expr_scope.
Notation "'λ'  x .. y , t" := (Abs (fun x => .. (Abs (fun y => t%expr)) ..)) : expr_scope.
Notation "'$' x" := (Var x) (at level 10, format "'$' x") : expr_scope.
Notation "0" := (#O)%expr : expr_scope.
Notation "n '.+1'" := (#S @ n)%expr (at level 10, format "n '.+1'") : expr_scope.
Notation "x + y" := (#Add @ x @ y)%expr : expr_scope.
Notation "( x , y , .. , z )" := (#Pair @ .. (#Pair @ x @ y) .. @ z)%expr : expr_scope.
Notation "x :: xs" := (#Cons @ x @ xs)%expr : expr_scope.
Notation "xs ++ ys" := (#ListApp @ xs @ ys)%expr : expr_scope.
Notation "[ ]" := (#Nil)%expr : expr_scope.
Notation "[ x ]" := (x :: [])%expr : expr_scope.
Notation "[ x ; y ; .. ; z ]" :=  (#Cons @ x @ (#Cons @ y @ .. (#Cons @ z @ []) ..))%expr : expr_scope.


Delimit Scope pattern_scope with pattern.
Bind Scope pattern_scope with pattern.
Notation "#?" := pLiteral : pattern_scope.
Notation "???{ t }" := (Wildcarde (Some t)) (format "???{ t }") : pattern_scope.
Notation "??{ t }" := (Wildcardv t) (format "??{ t }") : pattern_scope.
Notation "??" := (Wildcarde None) : pattern_scope.
Notation "??ℕ" := (Wildcarde (Some (Base Nat))) : pattern_scope.
Notation "??ℕℕ" := (Wildcarde (Some (Base (Prod Nat Nat)))) : pattern_scope.
Notation "# idc" := (pIdent idc) : pattern_scope.
Infix "@" := pApp : pattern_scope.
Notation "0" := (#pO)%pattern : pattern_scope.
Notation "n '.+1'" := (#pS @ n)%pattern (at level 10, format "n '.+1'") : pattern_scope.
Notation "x + y" := (#pAdd @ x @ y)%pattern : pattern_scope.
Notation "( x , y , .. , z )" := (#pPair @ .. (#pPair @ x @ y) .. @ z)%pattern : pattern_scope.
Notation "x :: xs" := (#pCons @ x @ xs)%pattern : pattern_scope.
Notation "xs ++ ys" := (#pListApp @ xs @ ys)%pattern : pattern_scope.
Notation "[ ]" := (#pNil)%pattern : pattern_scope.
Notation "[ x ]" := (x :: [])%pattern : pattern_scope.
Notation "[ x ; y ; .. ; z ]" :=  (#pCons @ x @ (#pCons @ y @ .. (#pCons @ z @ []) ..))%pattern : pattern_scope.

Module type.
  Fixpoint try_make_transport_base_cps {T} (P : base_type -> Type) (t1 t2 : base_type)
           {struct t2}
  : (option (P t1 -> P t2) -> T) -> T
    := match t2, t1 with
       | Nat, Nat => fun k => k (Some (fun v => v))
       | List A, List A'
         => try_make_transport_base_cps
              (fun A => P (List A)) _ _
       | Prod s d, Prod s' d'
         => fun k
            => try_make_transport_base_cps
                 (fun s => P (Prod s _)) _ _
                 (fun trs
                  => match trs with
                     | Some trs
                       => try_make_transport_base_cps
                            (fun d => P (Prod _ d)) _ _
                            (fun trd
                             => match trd with
                                | Some trd => k (Some (fun v => trd (trs v)))
                                | None => k None
                                end)
                     | None => k None
                     end)
       | Nat, _
       | List _, _
       | Prod _ _, _
         => fun k => k None
       end.

  Fixpoint try_make_transport_cps {T} (P : type -> Type) (t1 t2 : type) {struct t2} : (option (P t1 -> P t2) -> T) -> T
    := match t2, t1 with
       | Base t2, Base t1
         => try_make_transport_base_cps P t1 t2
       | Arrow s d, Arrow s' d'
         => fun k
            => try_make_transport_cps
                 (fun s => P (Arrow s _)) _ _
                 (fun trs
                  => match trs with
                     | Some trs
                       => try_make_transport_cps
                            (fun d => P (Arrow _ d)) _ _
                            (fun trd
                             => match trd with
                                | Some trd => k (Some (fun v => trd (trs v)))
                                | None => k None
                                end)
                     | None => k None
                     end)
       | Base _, _
       | Arrow _ _, _
         => fun k => k None
       end.
  Definition try_transport_base_cps {T} (P : base_type -> Type) (t1 t2 : base_type) (v : P t1) (k : option (P t2) -> T) : T
    := try_make_transport_base_cps
         P t1 t2
         (fun tr
          => match tr with
             | Some tr => k (Some (tr v))
             | None => k None
             end).

  Definition try_transport_cps {T} (P : type -> Type) (t1 t2 : type) (v : P t1) (k : option (P t2) -> T) : T
    := try_make_transport_cps
         P t1 t2
         (fun tr
          => match tr with
             | Some tr => k (Some (tr v))
             | None => k None
             end).

(*
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
       | List A
         => fun v k
            => match t1 return P t1 -> _ with
               | List A'
                 => fun v
                    => try_transport_base_cps
                         (fun A => P (List A)) _ _ v
                         k
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
*)
  Definition try_transport (P : type -> Type) (t1 t2 : type) (v : P t1) : option (P t2)
    := try_transport_cps P t1 t2 v id.
End type.

Record > anyexpr {var : type -> Type}
  := wrap { anyexpr_ty : type ; unwrap :> @expr var anyexpr_ty }.
Arguments wrap {_ _} _.

Section with_var.
  Context {var : type -> Type}.
  Local Notation topexpr := expr.
  Local Notation topanyexpr := anyexpr.
  Local Notation expr := (@expr var).
  Local Notation anyexpr := (@anyexpr var).

  Fixpoint value (t : type)
    := match t with
       | Base _ as t
         => expr t
       | Arrow s d => value s -> value d
       end.

  Fixpoint reify {t} : value t -> expr t
    := match t return value t -> expr t with
       | Base t => fun v => v
       | Arrow s d
         => fun f => λ x , @reify d (f (@reflect s ($x)))
       end%expr
  with reflect {t} : expr t -> value t
       := match t return expr t -> value t with
          | Base t => fun v => v
          | Arrow s d
            => fun f x => @reflect d (f @ (@reify s x))
          end%expr.

  Inductive rawexpr : Type :=
  | rIdent {t} (idc : ident t) {t'} (alt : expr t')
  | rApp (f x : rawexpr) {t} (alt : expr t)
  | rLiteral (n : nat) {t} (alt : expr t)
  | rExpr {t} (e : expr t)
  | rValue {t} (e : value t).

  Definition type_of_rawexpr (e : rawexpr) : type
    := match e with
       | rIdent t idc t' alt => t'
       | rApp f x t alt => t
       | rLiteral n t alt => t
       | rExpr t e => t
       | rValue t e => t
       end.
  Definition expr_of_rawexpr (e : rawexpr) : expr (type_of_rawexpr e)
    := match e with
       | rIdent t idc t' alt => alt
       | rApp f x t alt => alt
       | rLiteral n t alt => alt
       | rExpr t e => e
       | rValue t e => reify e
       end.
  Definition value_of_rawexpr (e : rawexpr) : value (type_of_rawexpr e)
    := Eval cbv [expr_of_rawexpr] in
        match e with
        | rValue t e => e
        | e => reflect (expr_of_rawexpr e)
        end.
  Definition rValueOrExpr {t} : value t -> rawexpr
    := match t with
       | Base t => @rExpr t
       | Arrow _ _ => @rValue _
       end.

  Definition try_rExpr_cps {T t} (k : option rawexpr -> T) : expr t -> T
    := match t with
       | Base t => fun e => k (Some (rExpr e))
       | Arrow _ _ => fun _ => k None
       end.

  Definition reveal_rawexpr_cps {T}
             (k : rawexpr -> T)
             (e : rawexpr)
    : T
    := match e with
       | rExpr _ e as r
       | rValue (Base _) e as r
         => match e with
            | Ident t idc => k (rIdent idc e)
            | App s d f x => k (rApp (rExpr f) (rExpr x) e)
            | Literal n => k (rLiteral n e)
            | _ => k r
            end
       | e' => k e'
       end.

  Fixpoint pbase_interp (t : pbase_type) : Type
    := match t return Type with
       | pbAny => anyexpr
       | pNat => nat
       | pProd A B => pbase_interp A * pbase_interp B
       | pList A => list (pbase_interp A)
       end.

  Inductive quant_type := qforall | qexists.

  Fixpoint pbase_type_interp_cps (quant : quant_type) (t : pbase_type) (K : base_type -> Type) : Type
    := match t with
       | pbAny
         => match quant with
            | qforall => forall t : base_type, K t
            | qexists => { t : base_type & K t }
            end
       | pNat => K Nat
       | pProd A B
         => @pbase_type_interp_cps
              quant A
              (fun A'
               => @pbase_type_interp_cps
                    quant B (fun B' => K (Prod A' B')))
       | pList A
         => @pbase_type_interp_cps
              quant A (fun A' => K (List A'))
       end.

  Fixpoint ptype_interp_cps (quant : quant_type) (t : ptype) (kt : type -> type) (K : type -> Type) : Type
    := match t with
       | pBase t
         => pbase_type_interp_cps quant t (fun t => K (kt (Base t)))
       | pAny
         => match quant with
            | qforall => forall t : type, K (kt t)
            | qexists => { t : type & K (kt t) }
            end
       | pArrow None d
         => match quant with
            | qforall => forall t : base_type, @ptype_interp_cps quant d (fun d => kt (t -> d)%ctype) K
            | qexists => { t : base_type & @ptype_interp_cps quant d (fun d => kt (t -> d)%ctype) K }
            end
       | pArrow (Some t) d => @ptype_interp_cps quant d (fun d => kt (t -> d)%ctype) K
       end.

  Definition ptype_interp (quant : quant_type) (t : ptype) (K : Type -> Type) : Type
    := ptype_interp_cps quant t id (fun t => K (value t)).

  Fixpoint binding_dataT (p : pattern) : Type
    := match p return Type with
       | Wildcardv t => ptype_interp qexists t id
       | Wildcarde None => anyexpr
       | Wildcarde (Some t) => expr t
       | pIdent _ => unit
       | pApp f x => binding_dataT f * binding_dataT x
       | pLiteral => nat
       end%type.

  Fixpoint bind_base_cps {T t1 t2}
           (K : base_type -> Type)
           (k : option (pbase_type_interp_cps qexists t1 K) -> T)
           (v : K t2)
           {struct t1}
    : T
    := match t1 return (option (pbase_type_interp_cps qexists t1 K) -> T) -> T with
       | pbAny => fun k => k (Some (existT K t2 v))
       | pNat
         => fun k
            => match t2 return K t2 -> T with
               | Nat => fun v => k (Some v)
               | _ => fun _ => k None
               end v
       | pProd A B
         => fun k
            => match t2 return K t2 -> T with
               | Prod A' B'
                 => fun v
                    => @bind_base_cps
                         T B B' (fun B' => K (A' * B')%ctype)
                         (fun v'
                          => match v' with
                             | Some v''
                               => @bind_base_cps
                                    T A A' (fun A' => pbase_type_interp_cps qexists B (fun B' => K (A' * B')%ctype))
                                    k
                                    v''
                             | None => k None
                             end)
                         v
               | _ => fun _ => k None
               end v
       | pList A
         => fun k
            => match t2 return K t2 -> T with
               | List A'
                 => @bind_base_cps T A A' (fun A'' => K (List A'')) k
               | _ => fun _ => k None
               end v
       end k.

  Fixpoint bind_value_cps {T t1 t2}
           (kt : type -> type)
           (K := fun t => value (kt t))
           (k : option (ptype_interp_cps qexists t1 kt value) -> T)
           (v : K t2)
           {struct t1}
    : T
    := match t1 return (option (ptype_interp_cps qexists t1 kt value) -> T) -> T with
       | pBase t1
         => fun k
            => match t2 return K t2 -> T with
               | Base t2 => fun e => bind_base_cps K k e
               | Arrow _ _ => fun _ => k None
               end v
       | pAny => fun k => k (Some (existT _ t2 v))
       | pArrow None d
         => fun k
            => match t2 return K t2 -> T with
               | Base _ => fun _ => k None
               | Arrow (Base s) d'
                 => fun v
                    => @bind_value_cps
                         T d d' (fun d => kt (s -> d)%ctype)
                         (fun v'
                          => match v' with
                             | Some v'' => k (Some (existT _ s v''))
                             | None => k None
                             end)
                         v
               | Arrow _ _ => fun _ => k None
               end v
       | pArrow (Some s) d
         => fun k
            => match t2 return K t2 -> T with
               | Base _ => fun _ => k None
               | Arrow s' d'
                 => fun v
                    => type.try_transport_cps
                         (fun s => K (s -> _)%ctype) s' s v
                         (fun v'
                          => match v' with
                             | Some v''
                               => @bind_value_cps
                                    T d d' (fun d => kt (s -> d)%ctype)
                                    k
                                    v''
                             | None => k None
                             end)
               end v
       end k.

  Fixpoint bind_data_cps {T} (e : rawexpr) (p : pattern) {struct p}
    : (option (binding_dataT p) -> T) -> T
    := match p return (option (binding_dataT p) -> T) -> T with
       | Wildcardv t
         => fun k => bind_value_cps id k (value_of_rawexpr e)
       | Wildcarde None
         => fun k => k (Some (wrap (expr_of_rawexpr e)))
       | Wildcarde (Some _)
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
                       | rValue t e
                         => default tt
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

  Local Notation opt_anyexprP ivar
    := (fun should_do_again : bool => @topanyexpr (if should_do_again then ivar else var)).
  Local Notation opt_anyexpr ivar
    := (option (sigT (opt_anyexprP ivar))).

  Local Notation rewrite_rulesT' ivar
    := (list { p : pattern & binding_dataT p -> forall T, (opt_anyexpr ivar  -> T) -> T })
         (only parsing).

  Definition eval_rewrite_rules
             {ivar}
             (do_again : forall t, @topexpr ivar t -> expr t)
             (maybe_do_again
              := fun (should_do_again : bool) t
                 => if should_do_again return ((@topexpr (if should_do_again then ivar else var) t) -> expr t)
                    then do_again t
                    else id)
             (d : decision_tree)
             (rew : rewrite_rulesT' ivar)
             (e : rawexpr)
    : expr (type_of_rawexpr e)
    := eval_decision_tree
         (e::nil) d
         (fun k ctx default_on_rewrite_failure
          => match k, ctx return expr (type_of_rawexpr e) with
             | Some k', e'::nil
               => match nth_error rew k' return expr (type_of_rawexpr e) with
                  | Some (existT p f)
                    => bind_data_cps
                         e' p
                         (fun v
                          => match v with
                             | Some v
                               => f v _
                                    (fun fv
                                     => match fv return expr (type_of_rawexpr e) with
                                        | Some (existT should_do_again fv)
                                          => type.try_transport_cps
                                               _ _ _ (unwrap fv)
                                               (fun fv'
                                                => match fv', default_on_rewrite_failure with
                                                   | Some fv'', _
                                                     => maybe_do_again should_do_again _ fv''
                                                   | None, Some default => default tt
                                                   | None, None => expr_of_rawexpr e
                                                   end)
                                        | None => match default_on_rewrite_failure with
                                                  | Some default => default tt
                                                  | None => expr_of_rawexpr e
                                                  end
                                        end)
                             | None => expr_of_rawexpr e
                             end)
                  | None => expr_of_rawexpr e
                  end
             | _, _ => expr_of_rawexpr e
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
                         | Wildcarde _ | Wildcardv _ => None
                         | _ => Some n
                         end)
         (enumerate p).

  Definition filter_pattern_wildcard (p : list (nat * list pattern)) : list (nat * list pattern)
    := filter (fun '(_, p) => match p with
                              | Wildcarde _::_ => true
                              | Wildcardv _::_ => true
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
       | (n, Wildcarde _::ps)
       | (n, Wildcardv _::ps)
       | (n, pLiteral::ps)
         => Some (n, ps)
       | (_, pIdent _::_)
       | (_, pApp _ _::_)
       | (_, nil)
         => None
       end.

  Definition refine_pattern_app (p : nat * list pattern) : option (nat * list pattern)
    := match p with
       | (n, Wildcarde _::ps)
       | (n, Wildcardv _::ps)
         => Some (n, Wildcarde None :: Wildcarde None :: ps)
       | (n, pApp f x :: ps)
         => Some (n, f :: x :: ps)
       | (_, pLiteral::_)
       | (_, pIdent _::_)
       | (_, nil)
         => None
       end.

  Definition refine_pattern_pident (pidc : pident) (p : nat * list pattern) : option (nat * list pattern)
    := match p with
       | (n, Wildcarde _::ps)
       | (n, Wildcardv _::ps)
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

  Definition compile_rewrites {ivar} (fuel : nat) (ps : rewrite_rulesT' ivar)
    := compile_rewrites' fuel (enumerate (List.map (fun p => projT1 p :: nil) ps)).

  Fixpoint with_bindingsT (p : pattern) (T : Type)
    := match p return Type with
       | Wildcarde (Some t) => expr t -> T
       | Wildcarde None => forall t, expr t -> T
       | Wildcardv t => ptype_interp qforall t (fun eT => eT -> T)
       | pLiteral => nat -> T
       | pApp f x => with_bindingsT f (with_bindingsT x T)
       | pIdent _ => T
       end.

  Fixpoint lift_pbase_type_interp_cps {K1 K2} {quant} (F : forall t : base_type, K1 t -> K2 t) {t}
    : pbase_type_interp_cps quant t K1
      -> pbase_type_interp_cps quant t K2
    := match t, quant return pbase_type_interp_cps quant t K1
                             -> pbase_type_interp_cps quant t K2 with
       | pbAny, qforall => fun f t => F t (f t)
       | pbAny, qexists => fun tf => existT _ _ (F _ (projT2 tf))
       | pNat, _ => F _
       | pProd A B, _
         => @lift_pbase_type_interp_cps
              _ _ quant
              (fun A'
               => @lift_pbase_type_interp_cps
                    _ _ quant (fun _ => F _) B)
              A
       | pList A, _
         => @lift_pbase_type_interp_cps
              _ _ quant (fun _ => F _) A
       end.

  Fixpoint lift_ptype_interp_cps {A B : Type} {quant kt} (F : A -> B) {t}
    : ptype_interp_cps quant t kt (fun eT => value eT -> A)
      -> ptype_interp_cps quant t kt (fun eT => value eT -> B)
    := match t, quant return ptype_interp_cps quant t kt (fun eT => value eT -> A)
                             -> ptype_interp_cps quant t kt (fun eT => value eT -> B) with
       | pAny, qforall => fun f t x => F (f t x)
       | pAny, qexists => fun tf => existT (fun t => value (kt t) -> B)
                                           _
                                           (fun x => F (projT2 tf x))
       | pBase t, _
         => lift_pbase_type_interp_cps
              (K1:=fun eT => _ -> A)
              (K2:=fun eT => _ -> B)
              (fun _ f x => F (f x))
       | pArrow None d, qforall
         => fun f t
            => @lift_ptype_interp_cps _ _ _ (fun d => kt (_ -> d)%ctype) F d (f t)
       | pArrow None d, qexists
         => fun tf
            => existT _
                      (projT1 tf)
                      (@lift_ptype_interp_cps _ _ _ (fun d => kt (_ -> d)%ctype) F d (projT2 tf))
       | pArrow (Some s) d, _
         => @lift_ptype_interp_cps _ _ _ (fun d => kt (_ -> d)%ctype) F d
       end.

  Fixpoint lift_with_bindings {p} {A B : Type} (F : A -> B) {struct p} : with_bindingsT p A -> with_bindingsT p B
    := match p return with_bindingsT p A -> with_bindingsT p B with
       | Wildcarde (Some _) => fun f e => F (f e)
       | Wildcarde None => fun f _ e => F (f _ e)
       | Wildcardv t => lift_ptype_interp_cps F
       | pLiteral => fun f e => F (f e)
       | pApp f x
         => @lift_with_bindings
              f _ _
              (@lift_with_bindings x _ _ F)
       | pIdent _
         => F
       end.

  Fixpoint app_pbase_type_interp_cps {T : Type} {K1 K2 : base_type -> Type}
           (F : forall t, K1 t -> K2 t -> T)
           {t}
    : pbase_type_interp_cps qforall t K1
      -> pbase_type_interp_cps qexists t K2 -> T
    := match t return pbase_type_interp_cps qforall t K1
                      -> pbase_type_interp_cps qexists t K2 -> T with
       | pbAny => fun f tv => F _ (f _) (projT2 tv)
       | pNat => fun f v => F _ f v
       | pProd A B
         => @app_pbase_type_interp_cps
              _
              (fun A' => pbase_type_interp_cps qforall B (fun B' => K1 (A' * B')%ctype))
              (fun A' => pbase_type_interp_cps qexists B (fun B' => K2 (A' * B')%ctype))
              (fun A'
               => @app_pbase_type_interp_cps
                    _
                    (fun B' => K1 (A' * B')%ctype)
                    (fun B' => K2 (A' * B')%ctype)
                    (fun _ => F _)
                    B)
              A
       | pList A
         => @app_pbase_type_interp_cps T (fun A' => K1 (List A')) (fun A' => K2 (List A')) (fun _ => F _) A
       end.

  Fixpoint app_ptype_interp_cps {T : Type} {kt : type -> type} {K : type -> Type}
           {t}
    : ptype_interp_cps qforall t kt (fun eT => K eT -> T)
      -> ptype_interp_cps qexists t kt K -> T
    := match t return ptype_interp_cps qforall t kt (fun eT => K eT -> T)
                      -> ptype_interp_cps qexists t kt K -> T with
       | pAny => fun f tv => f _ (projT2 tv)
       | pBase t
         => app_pbase_type_interp_cps
              (K1:=fun t => K (kt t) -> T)
              (K2:=fun t => K (kt t))
              (fun _ f v => f v)
       | pArrow (Some s) d
         => @app_ptype_interp_cps T (fun d => kt (_ -> d)%ctype) K d
       | pArrow None d
         => fun f tv
            => @app_ptype_interp_cps T (fun d => kt (_ -> d)%ctype) K d (f _) (projT2 tv)
       end.

  Fixpoint app_binding_data {T p} : forall (f : with_bindingsT p T) (v : binding_dataT p), T
    := match p return forall (f : with_bindingsT p T) (v : binding_dataT p), T with
       | Wildcarde (Some _)
       | pLiteral
         => fun f => f
       | Wildcarde None
         => fun f v => f _ (unwrap v)
       | Wildcardv t
         => app_ptype_interp_cps
       | pApp f x
         => fun F '(vf, vx)
            => @app_binding_data _ x (@app_binding_data _ f F vf) vx
       | pIdent _
         => fun f 'tt => f
       end.

  Definition reify_list {t : base_type} (ls : list (expr t)) : expr (List t)
    := fold_right
         (fun x xs => x :: xs)%expr
         []%expr
         ls.

  Fixpoint reflect_list_cps {t} (e : expr t) T
    : (option (list (expr match t return base_type with
                          | Base (List t) => t
                          | _ => Nat
                          end)) -> T)
      -> T
    := match e in topexpr t
             return (option (list (expr match t return base_type with
                                        | Base (List t) => t
                                        | _ => Nat
                                        end)) -> T)
                    -> T with
       | [] => fun k => k (Some nil)
       | x :: xs
         => fun k
            => @reflect_list_cps
                 _ xs T
                 (fun xs'
                  => match xs' with
                     | Some xs'
                       => type.try_transport_base_cps
                            (fun t => list (expr t)) _ _ xs'
                            (fun xs'
                             => match xs' with
                                | Some xs'
                                  => type.try_transport_cps
                                       _ _ _ x
                                       (fun x
                                        => match x with
                                           | Some x'
                                             => k (Some (x' :: xs')%list)
                                           | None => k None
                                           end)
                                | None => k None
                                end)
                     | None => k None
                     end)
       | _ => fun k => k None
       end%expr.
  Arguments reflect_list_cps {t} e [T] _.

  (** XXX MOVEME *)
  Definition continuation A := forall T, (A -> T) -> T.
  Definition bind_continuation {A B} (x : continuation A) (f : A -> continuation B) : continuation B
    := fun T k => x _ (fun x' => f x' T k).
  Definition option_bind_continuation {A B} (x : continuation (option A)) (f : A -> continuation (option B)) : continuation (option B)
    := bind_continuation x (fun x' T k => match x' with
                                          | Some x' => f x' T k
                                          | None => k None
                                          end).
  Delimit Scope continuation_scope with continuation.
  Bind Scope continuation_scope with continuation.
  Notation "v <- x ; f" := (bind_continuation x (fun v => f%continuation)) : continuation_scope.
  Notation "v <-- x ; f" := (option_bind_continuation x (fun v => f%continuation)) : continuation_scope.
  Definition mkcast {P : type -> Type} {t1 t2 : type} : continuation (option (P t1 -> P t2))
    := fun T k => type.try_make_transport_cps P t1 t2 k.
  Definition cast {P : type -> Type} {t1 t2 : type} (v : P t1) : continuation (option (P t2))
    := fun T k => type.try_transport_cps P t1 t2 v k.
  Definition ret {A} (v : A) : continuation A := fun T k => k v.
  Definition oret {A} (v : A) : continuation (option A) := fun T k => k (Some v).
  Notation make_rewrite'_cps p f
    := (existT
          (fun p' : pattern => binding_dataT p' -> continuation (opt_anyexpr value))
          p%pattern
          (fun v T (k : opt_anyexpr value -> T)
           => @app_binding_data _ p%pattern f%expr v T k)).
  Notation make_rewrite' p f
    := (existT
          (fun p' : pattern => binding_dataT p' -> continuation (opt_anyexpr value))
          p%pattern
          (fun v T (k : opt_anyexpr value -> T)
           => k (@app_binding_data _ p%pattern f%expr v))).
  Notation make_rewrite p f
    := (let f' := (@lift_with_bindings p _ _ (fun x:anyexpr => Some (existT (opt_anyexprP value) false x)) f%expr) in
        make_rewrite' p f').
  Notation make_rewrite_step p f
    := (let f' := (@lift_with_bindings p _ _ (fun x:@topanyexpr value => Some (existT (opt_anyexprP value) true x)) f%expr) in
        make_rewrite' p f').
  Notation make_rewrite_cps p f
    := (let f' := (@lift_with_bindings p _ _ (fun x:continuation (option anyexpr) => (x' <-- x; oret (existT (opt_anyexprP value) false x'))%continuation) f%expr) in
        make_rewrite'_cps p f').
  Notation make_rewrite_step_cps p f
    := (let f' := (@lift_with_bindings p _ _ (fun x:continuation (option (@topanyexpr value)) => (x' <-- x; oret (existT (opt_anyexprP value) true x'))%continuation) f%expr) in
        make_rewrite'_cps p f').
About ListFoldRight.
  Definition rewrite_rules : rewrite_rulesT' value
    := [make_rewrite (0 + ??ℕ) (fun x => x);
          make_rewrite (??ℕ + 0) (fun x => x);
          make_rewrite (#? + #?) (fun x y => ##(x + y));
          make_rewrite (#? + ??ℕ.+1) (fun x y => ##(Datatypes.S x) + y);
          make_rewrite (??ℕ.+1 + #?) (fun x y => x + ##(Datatypes.S y));
          make_rewrite (??ℕ.+1 + ??ℕ.+1) (fun x y => (x+y).+1.+1);
          make_rewrite (??ℕ.+1 + ??ℕ) (fun x y => (x+y).+1);
          make_rewrite (??ℕ + ??ℕ.+1) (fun x y => (x+y).+1);
          make_rewrite (#pFst @ (??, ??)) (fun tx x ty y => x);
          make_rewrite (#pSnd @ (??, ??)) (fun tx x ty y => y);
          make_rewrite_cps
            (??{pList ??} ++ ??{pList ??})
            (fun _ xs _ ys
             => xs <-- @cast expr _ (List _) xs;
                xs <-- reflect_list_cps xs;
                ys <-- reflect_list_cps ys;
                oret (wrap (reify_list (List.app xs ys))));
          make_rewrite_step_cps
            (#pListFlatMap @ ??{?? -> pList ??} @ ??{pList ??})
            (fun _ _ f _ xs
             => xs <-- @cast expr _ (List _) xs;
                  xs <-- reflect_list_cps xs;
                  oret (wrap (#ListFoldRight @ (λ ls1 ls2, $ls1 ++ $ls2) @ [] @ $(reify_list (List.map (fun x => f x) xs))%expr)));
          make_rewrite_cps
            (#pListFoldRight @ ??{?? -> ?? -> ??} @ ??{pBase ??} @ ??{pList ??})
            (fun _ _ _ f A init B xs
             => f <-- @cast value _ (B -> A -> A)%ctype f;
                  xs <-- reflect_list_cps xs;
                  oret (wrap (fold_right f init xs)));
          make_rewrite_cps
            (#pListRect @ ??{pBase ??} @ ??{?? -> ?? -> ?? -> ??} @ ??{pList ??})
            (fun P Pnil _ _ _ _ Pcons A xs
             => Pcons <-- @cast value _ (A -> List A -> P -> P)%ctype Pcons;
                  xs <-- reflect_list_cps xs;
                  oret (wrap (list_rect
                                (fun _ => expr P)
                                Pnil
                                (fun x' xs' rec => Pcons x' (reify_list xs') rec)
                                xs)));
          make_rewrite_cps
            (#pListMap @ ??{?? -> pBase ??} @ ??{pList ??})
            (fun _ _ f _ xs
             => xs <-- @cast expr _ (List _) xs;
                  xs <-- reflect_list_cps xs;
                  oret (wrap (reify_list (List.map f xs))));
          make_rewrite_cps
            (#pListMap @ ??{?? -> pBase ??} @ (?? :: ??))
            (fun _ _ f _ x _ xs
             => xs <-- @cast expr _ (List _) xs;
                  x <-- cast x;
                  oret (wrap (f x :: #ListMap @ (λ v , f ($v)) @ xs))%expr)
       ]%list%pattern%continuation%option.

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
  Definition default_fuel := Eval compute in List.length rewrite_rules.

  Section with_do_again.
    Context (do_again : forall t, @topexpr value t -> expr t).

    Definition dorewrite1 (e : rawexpr) : expr (type_of_rawexpr e)
      := eval_rewrite_rules do_again dtree rewrite_rules e.

    Fixpoint do_rewrite_ident (t : type) : forall e : rawexpr, (forall P, P (type_of_rawexpr e) -> P t) -> value t
      := match t return forall e : rawexpr, (forall P, P (type_of_rawexpr e) -> P t) -> value t with
         | Base _
           => fun e k => k _ (dorewrite1 e)
         | Arrow s d
           => fun f k x => @do_rewrite_ident d (rApp f (rValueOrExpr x) (k _ (expr_of_rawexpr f) @ reify x))%expr (fun _ => id)
         end.

    Fixpoint dorewrite' {t} (e : @topexpr value t) : value t
      := match e in topexpr t return value t with
         | Ident t idc
           => eta_ident_cps idc (fun t' idc' => do_rewrite_ident t' (rIdent idc' #idc') (fun _ => id))
         | App s d f x => @dorewrite' _ f (@dorewrite' _ x)
         | Literal n => Literal n
         | Var t v => v
         | Abs s d f => fun x : value s => @dorewrite' d (f x)
         end.

    Fixpoint nbe {t} (e : @topexpr value t) : value t
      := match e in topexpr t return value t with
         | Abs s d f => fun x : value s => @nbe d (f x)
         | App s d f x => @nbe _ f (@nbe _ x)
         | Var t v => v
         | Ident t idc => reflect (Ident idc)
         | Literal n => Literal n
         end.
  End with_do_again.
End with_var.

Fixpoint dorewrite'' (fuel : nat) {var t} e : @value var t
  := @dorewrite'
       var
       (fun t' e'
        => match fuel with
           | Datatypes.O
             => reify (nbe e')
           | Datatypes.S fuel' => reify (@dorewrite'' fuel' var t' e')
           end)
       t e.

Arguments bind_data_cps / .
Arguments dorewrite1 / .
Arguments dorewrite' / .
Arguments dorewrite'' / .
Arguments default_fuel / .
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
Arguments bind_value_cps / .
Arguments bind_base_cps / .
Arguments app_ptype_interp_cps / .
Arguments app_binding_data / .
Arguments anyexpr_ty / .
Arguments unwrap / .
Arguments type_of_rawexpr / .
Arguments expr_of_rawexpr / .
Arguments reveal_rawexpr_cps / .
Arguments type.try_transport_cps _ _ !_ !_ / .
Arguments type.try_transport_base_cps _ _ !_ !_ / .
Arguments type.try_make_transport_cps _ _ !_ !_.
Arguments type.try_make_transport_base_cps _ _ !_ !_.
Arguments orb_pident / .
Arguments or_opt_pident / .
Arguments rValueOrExpr / .
Arguments Some_t / .
Arguments value_of_rawexpr / .
Arguments cast / .
Arguments ret / .
Arguments oret / .
Arguments bind_continuation / .
Arguments option_bind_continuation / .
Arguments lift_ptype_interp_cps / .
Arguments lift_pbase_type_interp_cps / .
Arguments app_pbase_type_interp_cps / .
Arguments option_type / .
Arguments pbase_type_interp_cps / .
Arguments ptype_interp / .
Arguments ptype_interp_cps / .
Arguments default_fuel / .
Set Printing Depth 1000000.
Definition dorewrite''' {var}
  := Eval cbv (*-[value reify default_fuel reflect nbe type.try_transport_base_cps type.try_make_transport_base_cps type.try_make_transport_cps Nat.add List.map list_rect reify reflect reify_list reflect_list_cps List.app]*) (* but we also need to exclude things in the rhs of the rewrite rule *)
          [id orb projT1 projT2 nth_error set_nth update_nth anyexpr_ty app_binding_data app_pbase_type_interp_cps app_ptype_interp_cps bind_base_cps bind_continuation bind_data_cps binding_dataT bind_value_cps cast continuation dorewrite' dorewrite'' dorewrite1 do_rewrite_ident dtree eta_ident_cps eval_decision_tree eval_rewrite_rules expr_of_rawexpr lift_pbase_type_interp_cps lift_ptype_interp_cps lift_with_bindings option_bind_continuation orb_pident oret or_opt_pident pbase_type_interp_cps pident_ident_beq pident_of_ident ptype_interp ptype_interp_cps reveal_rawexpr_cps rewrite_rules rValueOrExpr swap_list type_of_rawexpr type.try_transport_cps unwrap value_of_rawexpr with_bindingsT]
    in @dorewrite'' default_fuel var.
Arguments dorewrite''' / .
Definition dorewrite
  := Eval cbn [dorewrite''' type.try_transport_cps type.try_transport_base_cps type.try_make_transport_cps type.try_make_transport_base_cps Option.bind reify reflect nbe (*default_fuel*)] in @dorewrite'''.
Arguments dorewrite {var t} e.
Local Open Scope expr_scope.
Arguments expr : clear implicits.
Print dorewrite.
(*dorewrite =
fun var : type -> Type =>
(fix dorewrite'' (fuel : nat) (var0 : type -> Type) (t : type) (e : expr value t) {struct fuel} : value t :=
   (fix dorewrite' (t0 : type) (e0 : expr value t0) {struct e0} : value t0 :=
      match e0 in (expr _ t1) return (value t1) with
      | $v => v
      | @Abs _ s d f => fun x : value s => dorewrite' d (f x)
      | #(idc) =>
          match idc in (ident t2) return (value t2) with
          | O => 0
          | S => fun x : expr var0 Nat => x.+1
          | Add =>
              fun x x0 : expr var0 Nat =>
              match x with
              | @Abs _ _ _ _ =>
                  match x0 with
                  | 0 => x
                  | @App _ s0 _ #(S) x1 =>
                      type.try_make_transport_cps (expr var0) s0 Nat
                        (fun tr : option (expr var0 s0 -> expr var0 Nat) =>
                         match tr with
                         | Some tr0 => (x + tr0 x1).+1
                         | None => x + x0
                         end)
                  | @App _ s0 _ ($_) _ | @App _ s0 _ (@Abs _ _ _ _) _ | @App _ s0 _ 0 _ | @App _ s0 _ #(Add) _ | @App _ s0 _
                    #(@Pair _ _) _ | @App _ s0 _ #(@Fst _ _) _ | @App _ s0 _ #(@Snd _ _) _ | @App _ s0 _ [] _ | @App _ s0 _ #
                    (@Cons _) _ | @App _ s0 _ #(@ListMap _ _) _ | @App _ s0 _ #(@ListApp _) _ | @App _ s0 _ #
                    (@ListFlatMap _ _) _ | @App _ s0 _ #(@ListRect _ _) _ | @App _ s0 _ #(@ListFoldRight _ _) _ | @App _ s0 _
                    (_ @ _) _ | @App _ s0 _ ##(_) _ => x + x0
                  | _ => x + x0
                  end
              | 0 => x0
              | @App _ s _ f x1 =>
                  match x0 with
                  | 0 => x
                  | @App _ s0 _ #(S) x2 =>
                      match f with
                      | #(S) =>
                          type.try_make_transport_cps (expr var0) s Nat
                            (fun tr : option (expr var0 s -> expr var0 Nat) =>
                             match tr with
                             | Some tr0 =>
                                 type.try_make_transport_cps (expr var0) s0 Nat
                                   (fun tr1 : option (expr var0 s0 -> expr var0 Nat) =>
                                    match tr1 with
                                    | Some tr2 => ((tr0 x1 + tr2 x2).+1).+1
                                    | None => x + x0
                                    end)
                             | None => x + x0
                             end)
                      | _ =>
                          type.try_make_transport_cps (expr var0) s0 Nat
                            (fun tr : option (expr var0 s0 -> expr var0 Nat) =>
                             match tr with
                             | Some tr0 => (x + tr0 x2).+1
                             | None => x + x0
                             end)
                      end
                  | @App _ s0 _ ($_) _ | @App _ s0 _ (@Abs _ _ _ _) _ | @App _ s0 _ 0 _ | @App _ s0 _ #(Add) _ | @App _ s0 _
                    #(@Pair _ _) _ | @App _ s0 _ #(@Fst _ _) _ | @App _ s0 _ #(@Snd _ _) _ | @App _ s0 _ [] _ | @App _ s0 _ #
                    (@Cons _) _ | @App _ s0 _ #(@ListMap _ _) _ | @App _ s0 _ #(@ListApp _) _ | @App _ s0 _ #
                    (@ListFlatMap _ _) _ | @App _ s0 _ #(@ListRect _ _) _ | @App _ s0 _ #(@ListFoldRight _ _) _ | @App _ s0 _
                    (_ @ _) _ | @App _ s0 _ ##(_) _ =>
                      match f with
                      | #(S) =>
                          type.try_make_transport_cps (expr var0) s Nat
                            (fun tr : option (expr var0 s -> expr var0 Nat) =>
                             match tr with
                             | Some tr0 => (tr0 x1 + x0).+1
                             | None => x + x0
                             end)
                      | _ => x + x0
                      end
                  | ##(n) =>
                      match f with
                      | #(S) =>
                          type.try_make_transport_cps (expr var0) s Nat
                            (fun tr : option (expr var0 s -> expr var0 Nat) =>
                             match tr with
                             | Some tr0 => tr0 x1 + ##(Datatypes.S n)
                             | None => x + x0
                             end)
                      | _ => x + x0
                      end
                  | _ =>
                      match f with
                      | #(S) =>
                          type.try_make_transport_cps (expr var0) s Nat
                            (fun tr : option (expr var0 s -> expr var0 Nat) =>
                             match tr with
                             | Some tr0 => (tr0 x1 + x0).+1
                             | None => x + x0
                             end)
                      | _ => x + x0
                      end
                  end
              | ##(n) =>
                  match x0 with
                  | 0 => x
                  | @App _ s _ #(S) x1 =>
                      type.try_make_transport_cps (expr var0) s Nat
                        (fun tr : option (expr var0 s -> expr var0 Nat) =>
                         match tr with
                         | Some tr0 => ##(Datatypes.S n) + tr0 x1
                         | None => x + x0
                         end)
                  | @App _ s _ ($_) _ | @App _ s _ (@Abs _ _ _ _) _ | @App _ s _ 0 _ | @App _ s _ #(Add) _ | @App _ s _ #
                    (@Pair _ _) _ | @App _ s _ #(@Fst _ _) _ | @App _ s _ #(@Snd _ _) _ | @App _ s _ [] _ | @App _ s _ #
                    (@Cons _) _ | @App _ s _ #(@ListMap _ _) _ | @App _ s _ #(@ListApp _) _ | @App _ s _ #(@ListFlatMap _ _) _ | @App _
                    s _ #(@ListRect _ _) _ | @App _ s _ #(@ListFoldRight _ _) _ | @App _ s _ (_ @ _) _ | @App _ s _ ##
                    (_) _ => x + x0
                  | ##(n0) => ##(n + n0)
                  | _ => x + x0
                  end
              | _ =>
                  match x0 with
                  | 0 => x
                  | @App _ s _ #(S) x1 =>
                      type.try_make_transport_cps (expr var0) s Nat
                        (fun tr : option (expr var0 s -> expr var0 Nat) =>
                         match tr with
                         | Some tr0 => (x + tr0 x1).+1
                         | None => x + x0
                         end)
                  | @App _ s _ ($_) _ | @App _ s _ (@Abs _ _ _ _) _ | @App _ s _ 0 _ | @App _ s _ #(Add) _ | @App _ s _ #
                    (@Pair _ _) _ | @App _ s _ #(@Fst _ _) _ | @App _ s _ #(@Snd _ _) _ | @App _ s _ [] _ | @App _ s _ #
                    (@Cons _) _ | @App _ s _ #(@ListMap _ _) _ | @App _ s _ #(@ListApp _) _ | @App _ s _ #(@ListFlatMap _ _) _ | @App _
                    s _ #(@ListRect _ _) _ | @App _ s _ #(@ListFoldRight _ _) _ | @App _ s _ (_ @ _) _ | @App _ s _ ##
                    (_) _ => x + x0
                  | _ => x + x0
                  end
              end
          | @Pair A B => fun (x : expr var0 A) (x0 : expr var0 B) => (x, x0)
          | @Fst A B =>
              fun x : expr var0 (A * B) =>
              match x with
              | @App _ s0 _ #(@Pair _ _) x1 @ _ =>
                  type.try_make_transport_cps (expr var0) s0 A
                    (fun tr : option (expr var0 s0 -> expr var0 A) => match tr with
                                                                      | Some tr0 => tr0 x1
                                                                      | None => #(Fst) @ x
                                                                      end)
              | @App _ s0 _ ($_) _ @ _ | @App _ s0 _ (@Abs _ _ _ _) _ @ _ | @App _ s0 _ 0 _ @ _ | @App _ s0 _ #(S) _ @ _ |
                @App _ s0 _ #(Add) _ @ _ | @App _ s0 _ #(@Fst _ _) _ @ _ | @App _ s0 _ #(@Snd _ _) _ @ _ | @App _ s0 _ [] _ @ _ |
                @App _ s0 _ #(@Cons _) _ @ _ | @App _ s0 _ #(@ListMap _ _) _ @ _ | @App _ s0 _ #(@ListApp _) _ @ _ |
                @App _ s0 _ #(@ListFlatMap _ _) _ @ _ | @App _ s0 _ #(@ListRect _ _) _ @ _ | @App _ s0 _ #(@ListFoldRight _ _) _ @ _ |
                @App _ s0 _ (_ @ _) _ @ _ | @App _ s0 _ ##(_) _ @ _ => #(Fst) @ x
              | _ => #(Fst) @ x
              end
          | @Snd A B =>
              fun x : expr var0 (A * B) =>
              match x with
              | @App _ s _ (#(@Pair _ _) @ _) x0 =>
                  type.try_make_transport_cps (expr var0) s B
                    (fun tr : option (expr var0 s -> expr var0 B) => match tr with
                                                                     | Some tr0 => tr0 x0
                                                                     | None => #(Snd) @ x
                                                                     end)
              | @App _ s _ ($_) _ | @App _ s _ (@Abs _ _ _ _) _ | @App _ s _ #(_) _ | @App _ s _ ($_ @ _) _ | @App _ s _
                (@Abs _ _ _ _ @ _) _ | @App _ s _ (0 @ _) _ | @App _ s _ (_.+1) _ | @App _ s _ (#(Add) @ _) _ | @App _ s _
                (#(@Fst _ _) @ _) _ | @App _ s _ (#(@Snd _ _) @ _) _ | @App _ s _ ([] @ _) _ | @App _ s _ (#(@Cons _) @ _) _ | @App _ s
                _ (#(@ListMap _ _) @ _) _ | @App _ s _ (#(@ListApp _) @ _) _ | @App _ s _ (#(@ListFlatMap _ _) @ _) _ | @App _ s _
                (#(@ListRect _ _) @ _) _ | @App _ s _ (#(@ListFoldRight _ _) @ _) _ | @App _ s _ (_ @ _ @ _) _ | @App _ s _
                (##(_) @ _) _ | @App _ s _ ##(_) _ => #(Snd) @ x
              | _ => #(Snd) @ x
              end
          | @Nil A => []
          | @Cons A => fun (x : expr var0 A) (x0 : expr var0 (List A)) => x :: x0
          | @ListMap A B =>
              fun (x : expr var0 A -> expr var0 B) (x0 : expr var0 (List A)) =>
              type.try_make_transport_base_cps (fun A0 : base_type => expr var0 (List A0)) A A
                (fun tr : option (expr var0 (List A) -> expr var0 (List A)) =>
                 match tr with
                 | Some tr0 =>
                     reflect_list_cps (tr0 x0) (expr var0 (List B))
                       (fun x' : option (list (expr var0 A)) =>
                        match x' with
                        | Some x'0 =>
                            type.try_make_transport_base_cps (fun A0 : base_type => expr var0 (List A0)) B B
                              (fun tr1 : option (expr var0 (List B) -> expr var0 (List B)) =>
                               match tr1 with
                               | Some tr2 => tr2 (reify_list (map x x'0))
                               | None =>
                                   match x0 with
                                   | @App _ s _ (@App _ s0 _ #(@Cons _) x2) x1 =>
                                       type.try_make_transport_cps (expr var0) s (List A)
                                         (fun tr2 : option (expr var0 s -> expr var0 (List A)) =>
                                          match tr2 with
                                          | Some tr3 =>
                                              type.try_make_transport_cps (expr var0) s0 A
                                                (fun tr4 : option (expr var0 s0 -> expr var0 A) =>
                                                 match tr4 with
                                                 | Some tr5 =>
                                                     type.try_make_transport_base_cps (fun A1 : base_type => expr var0 (List A1)) B B
                                                       (fun tr6 : option (expr var0 (List B) -> expr var0 (List B)) =>
                                                        match tr6 with
                                                        | Some tr7 => tr7 (x (tr5 x2) :: #(ListMap) @ (λ v : var0 A,
                                                                                                       x ($v)) @ tr3 x1)
                                                        | None => #(ListMap) @ (λ x3 : var0 A,
                                                                                x ($x3)) @ x0
                                                        end)
                                                 | None => #(ListMap) @ (λ x3 : var0 A,
                                                                         x ($x3)) @ x0
                                                 end)
                                          | None => #(ListMap) @ (λ x3 : var0 A,
                                                                  x ($x3)) @ x0
                                          end)
                                   | @App _ s _ (@App _ s0 _ (_ @ _) _) _ => #(ListMap) @ (λ x4 : var0 A,
                                                                                           x ($x4)) @ x0
                                   | @App _ s _ (@App _ s0 _ ($_) _) _ | @App _ s _ (@App _ s0 _ (@Abs _ _ _ _) _) _ | @App _ s _
                                     (@App _ s0 _ 0 _) _ | @App _ s _ (@App _ s0 _ #(S) _) _ | @App _ s _ (@App _ s0 _ #(Add) _) _ |
                                     @App _ s _ (@App _ s0 _ #(@Pair _ _) _) _ | @App _ s _ (@App _ s0 _ #(@Fst _ _) _) _ | @App _ s _
                                     (@App _ s0 _ #(@Snd _ _) _) _ | @App _ s _ (@App _ s0 _ [] _) _ | @App _ s _
                                     (@App _ s0 _ #(@ListMap _ _) _) _ | @App _ s _ (@App _ s0 _ #(@ListApp _) _) _ | @App _ s _
                                     (@App _ s0 _ #(@ListFlatMap _ _) _) _ | @App _ s _ (@App _ s0 _ #(@ListRect _ _) _) _ | @App _ s _
                                     (@App _ s0 _ #(@ListFoldRight _ _) _) _ | @App _ s _ (@App _ s0 _ ##(_) _) _ =>
                                       #(ListMap) @ (λ x3 : var0 A,
                                                     x ($x3)) @ x0
                                   | @App _ s _ ($_) _ | @App _ s _ (@Abs _ _ _ _) _ | @App _ s _ #(_) _ | @App _ s _ ##(_) _ =>
                                       #(ListMap) @ (λ x2 : var0 A,
                                                     x ($x2)) @ x0
                                   | _ => #(ListMap) @ (λ x1 : var0 A,
                                                        x ($x1)) @ x0
                                   end
                               end)
                        | None =>
                            match x0 with
                            | @App _ s _ (@App _ s0 _ #(@Cons _) x2) x1 =>
                                type.try_make_transport_cps (expr var0) s (List A)
                                  (fun tr1 : option (expr var0 s -> expr var0 (List A)) =>
                                   match tr1 with
                                   | Some tr2 =>
                                       type.try_make_transport_cps (expr var0) s0 A
                                         (fun tr3 : option (expr var0 s0 -> expr var0 A) =>
                                          match tr3 with
                                          | Some tr4 =>
                                              type.try_make_transport_base_cps (fun A1 : base_type => expr var0 (List A1)) B B
                                                (fun tr5 : option (expr var0 (List B) -> expr var0 (List B)) =>
                                                 match tr5 with
                                                 | Some tr6 => tr6 (x (tr4 x2) :: #(ListMap) @ (λ v : var0 A,
                                                                                                x ($v)) @ tr2 x1)
                                                 | None => #(ListMap) @ (λ x3 : var0 A,
                                                                         x ($x3)) @ x0
                                                 end)
                                          | None => #(ListMap) @ (λ x3 : var0 A,
                                                                  x ($x3)) @ x0
                                          end)
                                   | None => #(ListMap) @ (λ x3 : var0 A,
                                                           x ($x3)) @ x0
                                   end)
                            | @App _ s _ (@App _ s0 _ (_ @ _) _) _ => #(ListMap) @ (λ x4 : var0 A,
                                                                                    x ($x4)) @ x0
                            | @App _ s _ (@App _ s0 _ ($_) _) _ | @App _ s _ (@App _ s0 _ (@Abs _ _ _ _) _) _ | @App _ s _
                              (@App _ s0 _ 0 _) _ | @App _ s _ (@App _ s0 _ #(S) _) _ | @App _ s _ (@App _ s0 _ #(Add) _) _ | @App _ s _
                              (@App _ s0 _ #(@Pair _ _) _) _ | @App _ s _ (@App _ s0 _ #(@Fst _ _) _) _ | @App _ s _
                              (@App _ s0 _ #(@Snd _ _) _) _ | @App _ s _ (@App _ s0 _ [] _) _ | @App _ s _
                              (@App _ s0 _ #(@ListMap _ _) _) _ | @App _ s _ (@App _ s0 _ #(@ListApp _) _) _ | @App _ s _
                              (@App _ s0 _ #(@ListFlatMap _ _) _) _ | @App _ s _ (@App _ s0 _ #(@ListRect _ _) _) _ | @App _ s _
                              (@App _ s0 _ #(@ListFoldRight _ _) _) _ | @App _ s _ (@App _ s0 _ ##(_) _) _ =>
                                #(ListMap) @ (λ x3 : var0 A,
                                              x ($x3)) @ x0
                            | @App _ s _ ($_) _ | @App _ s _ (@Abs _ _ _ _) _ | @App _ s _ #(_) _ | @App _ s _ ##(_) _ =>
                                #(ListMap) @ (λ x2 : var0 A,
                                              x ($x2)) @ x0
                            | _ => #(ListMap) @ (λ x1 : var0 A,
                                                 x ($x1)) @ x0
                            end
                        end)
                 | None =>
                     match x0 with
                     | @App _ s _ (@App _ s0 _ #(@Cons _) x2) x1 =>
                         type.try_make_transport_cps (expr var0) s (List A)
                           (fun tr0 : option (expr var0 s -> expr var0 (List A)) =>
                            match tr0 with
                            | Some tr1 =>
                                type.try_make_transport_cps (expr var0) s0 A
                                  (fun tr2 : option (expr var0 s0 -> expr var0 A) =>
                                   match tr2 with
                                   | Some tr3 =>
                                       type.try_make_transport_base_cps (fun A1 : base_type => expr var0 (List A1)) B B
                                         (fun tr4 : option (expr var0 (List B) -> expr var0 (List B)) =>
                                          match tr4 with
                                          | Some tr5 => tr5 (x (tr3 x2) :: #(ListMap) @ (λ v : var0 A,
                                                                                         x ($v)) @ tr1 x1)
                                          | None => #(ListMap) @ (λ x3 : var0 A,
                                                                  x ($x3)) @ x0
                                          end)
                                   | None => #(ListMap) @ (λ x3 : var0 A,
                                                           x ($x3)) @ x0
                                   end)
                            | None => #(ListMap) @ (λ x3 : var0 A,
                                                    x ($x3)) @ x0
                            end)
                     | @App _ s _ (@App _ s0 _ (_ @ _) _) _ => #(ListMap) @ (λ x4 : var0 A,
                                                                             x ($x4)) @ x0
                     | @App _ s _ (@App _ s0 _ ($_) _) _ | @App _ s _ (@App _ s0 _ (@Abs _ _ _ _) _) _ | @App _ s _
                       (@App _ s0 _ 0 _) _ | @App _ s _ (@App _ s0 _ #(S) _) _ | @App _ s _ (@App _ s0 _ #(Add) _) _ | @App _ s _
                       (@App _ s0 _ #(@Pair _ _) _) _ | @App _ s _ (@App _ s0 _ #(@Fst _ _) _) _ | @App _ s _
                       (@App _ s0 _ #(@Snd _ _) _) _ | @App _ s _ (@App _ s0 _ [] _) _ | @App _ s _ (@App _ s0 _ #(@ListMap _ _) _) _ |
                       @App _ s _ (@App _ s0 _ #(@ListApp _) _) _ | @App _ s _ (@App _ s0 _ #(@ListFlatMap _ _) _) _ | @App _ s _
                       (@App _ s0 _ #(@ListRect _ _) _) _ | @App _ s _ (@App _ s0 _ #(@ListFoldRight _ _) _) _ | @App _ s _
                       (@App _ s0 _ ##(_) _) _ => #(ListMap) @ (λ x3 : var0 A,
                                                                x ($x3)) @ x0
                     | @App _ s _ ($_) _ | @App _ s _ (@Abs _ _ _ _) _ | @App _ s _ #(_) _ | @App _ s _ ##(_) _ =>
                         #(ListMap) @ (λ x2 : var0 A,
                                       x ($x2)) @ x0
                     | _ => #(ListMap) @ (λ x1 : var0 A,
                                          x ($x1)) @ x0
                     end
                 end)
          | @ListApp A =>
              fun x x0 : expr var0 (List A) =>
              type.try_make_transport_base_cps (fun A0 : base_type => expr var0 (List A0)) A A
                (fun tr : option (expr var0 (List A) -> expr var0 (List A)) =>
                 match tr with
                 | Some tr0 =>
                     reflect_list_cps (tr0 x) (expr var0 (List A))
                       (fun x' : option (list (expr var0 A)) =>
                        match x' with
                        | Some x'0 =>
                            reflect_list_cps x0 (expr var0 (List A))
                              (fun x'1 : option (list (expr var0 A)) =>
                               match x'1 with
                               | Some x'2 =>
                                   type.try_make_transport_base_cps (fun A0 : base_type => expr var0 (List A0)) A A
                                     (fun tr1 : option (expr var0 (List A) -> expr var0 (List A)) =>
                                      match tr1 with
                                      | Some tr2 => tr2 (reify_list (x'0 ++ x'2))
                                      | None => x ++ x0
                                      end)
                               | None => x ++ x0
                               end)
                        | None => x ++ x0
                        end)
                 | None => x ++ x0
                 end)
          | @ListFlatMap A B =>
              fun (x : expr var0 A -> expr var0 (List B)) (x0 : expr var0 (List A)) =>
              type.try_make_transport_base_cps (fun A0 : base_type => expr var0 (List A0)) A A
                (fun tr : option (expr var0 (List A) -> expr var0 (List A)) =>
                 match tr with
                 | Some tr0 =>
                     reflect_list_cps (tr0 x0) (expr var0 (List B))
                       (fun x' : option (list (expr var0 A)) =>
                        match x' with
                        | Some x'0 =>
                            type.try_make_transport_base_cps (fun A0 : base_type => expr value (List A0)) B B
                              (fun tr1 : option (expr value (List B) -> expr value (List B)) =>
                               match tr1 with
                               | Some tr2 =>
                                   match fuel with
                                   | 0 =>
                                       nbe
                                         (tr2
                                            (#(ListFoldRight) @ (λ ls1 ls2 : value (List B),
                                                                 $ls1 ++ $ls2) @ [] @
                                             $(reify_list (map (fun x1 : expr var0 A => x x1) x'0))))
                                   | Datatypes.S fuel' =>
                                       dorewrite'' fuel' var0 (List B)
                                         (tr2
                                            (#(ListFoldRight) @ (λ ls1 ls2 : value (List B),
                                                                 $ls1 ++ $ls2) @ [] @
                                             $(reify_list (map (fun x1 : expr var0 A => x x1) x'0))))
                                   end
                               | None => #(ListFlatMap) @ (λ x1 : var0 A,
                                                           x ($x1)) @ x0
                               end)
                        | None => #(ListFlatMap) @ (λ x1 : var0 A,
                                                    x ($x1)) @ x0
                        end)
                 | None => #(ListFlatMap) @ (λ x1 : var0 A,
                                             x ($x1)) @ x0
                 end)
          | @ListRect A P =>
              fun (x : expr var0 P) (x0 : expr var0 A -> expr var0 (List A) -> expr var0 P -> expr var0 P) (x1 : expr var0 (List A)) =>
              type.try_make_transport_base_cps (fun x2 : base_type => value (x2 -> List A -> P -> P)) A A
                (fun trs : option (value (A -> List A -> P -> P) -> value (A -> List A -> P -> P)) =>
                 match trs with
                 | Some trs0 =>
                     type.try_make_transport_base_cps (fun A0 : base_type => value (A -> List A0 -> P -> P)) A A
                       (fun trs1 : option (value (A -> List A -> P -> P) -> value (A -> List A -> P -> P)) =>
                        match trs1 with
                        | Some trs2 =>
                            type.try_make_transport_base_cps (fun x2 : base_type => value (A -> List A -> x2 -> P)) P P
                              (fun trs3 : option (value (A -> List A -> P -> P) -> value (A -> List A -> P -> P)) =>
                               match trs3 with
                               | Some trs4 =>
                                   type.try_make_transport_base_cps (fun x2 : base_type => value (A -> List A -> P -> x2)) P P
                                     (fun trd : option (value (A -> List A -> P -> P) -> value (A -> List A -> P -> P)) =>
                                      match trd with
                                      | Some trd0 =>
                                          reflect_list_cps x1 (expr var0 P)
                                            (fun x' : option (list (expr var0 A)) =>
                                             match x' with
                                             | Some x'0 =>
                                                 type.try_make_transport_base_cps (fun x2 : base_type => expr var0 x2) P P
                                                   (fun tr : option (expr var0 P -> expr var0 P) =>
                                                    match tr with
                                                    | Some tr0 =>
                                                        tr0
                                                          (list_rect (fun _ : list (expr var0 A) => expr var0 P) x
                                                             (fun (x'1 : expr var0 A) (xs' : list (expr var0 A)) (rec : expr var0 P) =>
                                                              trd0 (trs4 (trs2 (trs0 x0))) x'1 (reify_list xs') rec) x'0)
                                                    | None =>
                                                        #(ListRect) @ x @
                                                        (λ (x2 : var0 A)(x3 : var0 (List A))(x4 : var0 P),
                                                         x0 ($x2) ($x3) ($x4)) @ x1
                                                    end)
                                             | None =>
                                                 #(ListRect) @ x @
                                                 (λ (x2 : var0 A)(x3 : var0 (List A))(x4 : var0 P),
                                                  x0 ($x2) ($x3) ($x4)) @ x1
                                             end)
                                      | None =>
                                          #(ListRect) @ x @ (λ (x2 : var0 A)(x3 : var0 (List A))(x4 : var0 P),
                                                             x0 ($x2) ($x3) ($x4)) @ x1
                                      end)
                               | None => #(ListRect) @ x @ (λ (x2 : var0 A)(x3 : var0 (List A))(x4 : var0 P),
                                                            x0 ($x2) ($x3) ($x4)) @ x1
                               end)
                        | None => #(ListRect) @ x @ (λ (x2 : var0 A)(x3 : var0 (List A))(x4 : var0 P),
                                                     x0 ($x2) ($x3) ($x4)) @ x1
                        end)
                 | None => #(ListRect) @ x @ (λ (x2 : var0 A)(x3 : var0 (List A))(x4 : var0 P),
                                              x0 ($x2) ($x3) ($x4)) @ x1
                 end)
          | @ListFoldRight A B =>
              fun (x : expr var0 B -> expr var0 A -> expr var0 A) (x0 : expr var0 A) (x1 : expr var0 (List B)) =>
              type.try_make_transport_base_cps (fun x2 : base_type => value (x2 -> A -> A)) B B
                (fun trs : option (value (B -> A -> A) -> value (B -> A -> A)) =>
                 match trs with
                 | Some trs0 =>
                     type.try_make_transport_base_cps (fun x2 : base_type => value (B -> x2 -> A)) A A
                       (fun trs1 : option (value (B -> A -> A) -> value (B -> A -> A)) =>
                        match trs1 with
                        | Some trs2 =>
                            type.try_make_transport_base_cps (fun x2 : base_type => value (B -> A -> x2)) A A
                              (fun trd : option (value (B -> A -> A) -> value (B -> A -> A)) =>
                               match trd with
                               | Some trd0 =>
                                   reflect_list_cps x1 (expr var0 A)
                                     (fun x' : option (list (expr var0 B)) =>
                                      match x' with
                                      | Some x'0 =>
                                          type.try_make_transport_base_cps (fun x2 : base_type => expr var0 x2) A A
                                            (fun tr : option (expr var0 A -> expr var0 A) =>
                                             match tr with
                                             | Some tr0 => tr0 (fold_right (trd0 (trs2 (trs0 x))) x0 x'0)
                                             | None => #(ListFoldRight) @ (λ (x2 : var0 B)(x3 : var0 A),
                                                                           x ($x2) ($x3)) @ x0 @ x1
                                             end)
                                      | None => #(ListFoldRight) @ (λ (x2 : var0 B)(x3 : var0 A),
                                                                    x ($x2) ($x3)) @ x0 @ x1
                                      end)
                               | None => #(ListFoldRight) @ (λ (x2 : var0 B)(x3 : var0 A),
                                                             x ($x2) ($x3)) @ x0 @ x1
                               end)
                        | None => #(ListFoldRight) @ (λ (x2 : var0 B)(x3 : var0 A),
                                                      x ($x2) ($x3)) @ x0 @ x1
                        end)
                 | None => #(ListFoldRight) @ (λ (x2 : var0 B)(x3 : var0 A),
                                               x ($x2) ($x3)) @ x0 @ x1
                 end)
          end
      | @App _ s d f x => dorewrite' (s -> d)%ctype f (dorewrite' s x)
      | ##(n) => ##(n)
      end) t e) default_fuel var
     : forall (var : type -> Type) (t : type), expr value t -> value t

Arguments var, t are implicit and maximally inserted
Argument scopes are [function_scope ctype_scope expr_scope]
*)
