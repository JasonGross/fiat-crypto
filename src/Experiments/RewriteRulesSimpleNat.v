Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.LetIn.
Import ListNotations.

Set Boolean Equality Schemes.
Inductive ctor :=
| O
| S
| Add.

Fixpoint ctor_beq_cps {T} (X Y : ctor) (k : bool -> T) {struct X} : T
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
| AppCtor (c : ctor) (args : list expr)
| Literal (n : nat).

Inductive pattern :=
| Wildcard
| pLiteral
| pCtor (c : ctor) (args : list pattern).

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
     | pCtor _ args
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
     | pCtor c args
       => fun k
          => match e with
             | AppCtor c' args'
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

Notation make_rewrite p f := (existT (fun p' : pattern => binding_dataT p' -> option expr) p%pattern f%expr).

Definition rewrite_rules : list { p : pattern & binding_dataT p -> option expr }
  := [make_rewrite (??.+1 + ??) (fun '((x, tt), (y, tt)) => Some ((x+y).+1));
        make_rewrite (?? + ??.+1) (fun '(x, ((y, tt), tt)) => Some ((x+y).+1));
        make_rewrite (0 + ??) (fun '(_, (x, tt)) => Some x);
        make_rewrite (?? + 0) (fun '(x, _) => Some x);
        make_rewrite (#? + #?) (fun '(x, (y, tt)) => Some (#(x + y)))]%list.

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
Print dorewrite.
