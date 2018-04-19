(* File reduced by coq-bug-finder from original input, then from 4431 lines to 3382 lines, then from 3059 lines to 2535 lines, then from 2589 lines to 2515 lines, then from 2606 lines to 2524 lines, then from 2682 lines to 2570 lines, then from 2715 lines to 2585 lines, then from 2720 lines to 2585 lines, then from 2644 lines to 2585 lines, then from 2675 lines to 2585 lines, then from 2687 lines to 2585 lines, then from 3027 lines to 2585 lines, then from 2715 lines to 2585 lines, then from 2685 lines to 2585 lines, then from 2763 lines to 2585 lines, then from 2647 lines to 2585 lines, then from 2692 lines to 2595 lines, then from 2781 lines to 2612 lines, then from 2700 lines to 2688 lines, then from 4973 lines to 2642 lines, then from 2758 lines to 2642 lines, then from 2728 lines to 2642 lines, then from 2806 lines to 2642 lines, then from 2690 lines to 2642 lines, then from 2717 lines to 2642 lines, then from 2701 lines to 2642 lines, then from 2667 lines to 2642 lines *)
(* coqc version 8.8+alpha (March 2018) compiled on Mar 16 2018 14:18:30 with OCaml 4.02.3
   coqtop version jgross-Leopard-WS:/home/jgross/Downloads/coq/coq-master,master (f21deb6c861b359f0d3bf8b170d277cfa0d80171) *)
Require Coq.FSets.FMapPositive.
Require Coq.micromega.Lia.
Global Set Asymmetric Patterns.
Reserved Notation "A <- X ; B" (at level 70, X at next level, right associativity, format "'[v' A  <-  X ; '/' B ']'").
Module Export Crypto_DOT_Util_DOT_Option.
  Module Export Crypto.
    Module Export Util.
      Module Export Option.
        Definition bind {A B} (v : option A) (f : A -> option B) : option B
          := match v with
             | Some v => f v
             | None => None
             end.

        Module Export Notations.
          Delimit Scope option_scope with option.
          Bind Scope option_scope with option.

          Notation "A <- X ; B" := (bind X (fun A => B%option)) : option_scope.
        End Notations.
        Local Open Scope option_scope.

      End Option.
    End Util.
  End Crypto.
End Crypto_DOT_Util_DOT_Option.
Module Export Crypto_DOT_Util_DOT_NatUtil.
  Module Export Crypto.
    Module Export Util.
      Module Export ListUtil.
        Import Coq.Lists.List.

        Definition list_case
                   {A} (P : list A -> Type) (N : P nil) (C : forall x xs, P (cons x xs))
                   (ls : list A)
          : P ls
          := match ls return P ls with
             | nil => N
             | cons x xs => C x xs
             end.

        Fixpoint update_nth {T} n f (xs:list T) {struct n} :=
	  match n with
	  | O => match xs with
		 | nil => nil
		 | x'::xs' => f x'::xs'
		 end
	  | S n' =>  match xs with
		     | nil => nil
		     | x'::xs' => x'::update_nth n' f xs'
		     end
          end.

      End ListUtil.
    End Util.
  End Crypto.
End Crypto_DOT_Util_DOT_NatUtil.
Module Export Crypto_DOT_Util_DOT_Notations.
  Module Export Crypto.
    Module Export Util.
      Module Export Notations.
        Reserved Infix "@" (left associativity, at level 11).
        Reserved Infix "@@" (left associativity, at level 11).
        Reserved Notation "A <-- X ; B" (at level 70, X at next level, right associativity, format "'[v' A  <--  X ; '/' B ']'").
        Reserved Notation "'expr_let' x := A 'in' b"
                 (at level 200, b at level 200, format "'expr_let'  x  :=  A  'in' '//' b").
        Reserved Notation "'λ' x .. y , t" (at level 200, x binder, y binder, right associativity, format "'λ'  x .. y , '//' t").
        Reserved Notation "A --->" (left associativity, at level 65).

      End Notations.

    End Util.

  End Crypto.

End Crypto_DOT_Util_DOT_Notations.
Module Export Crypto.
  Module Export Util.
    Module Export LetIn.

      Definition Let_In {A P} (x : A) (f : forall a : A, P a) : P x := let y := x in f y.

    End LetIn.

  End Util.

End Crypto.
Module Export Util.
  Module Export ZRange.
    Import Coq.ZArith.ZArith.

    Delimit Scope zrange_scope with zrange.
    Record zrange := { lower : Z ; upper : Z }.

    Module Export Notations.
      Notation "r[ l ~> u ]" := {| lower := l ; upper := u |} : zrange_scope.
    End Notations.

  End ZRange.

End Util.
Import Coq.ZArith.ZArith.

Module Export ZRange.
  Local Open Scope zrange_scope.

  Local Notation eta v := r[ lower v ~> upper v ].

  Definition union (x y : zrange) : zrange
    := let (lx, ux) := eta x in
       let (ly, uy) := eta y in
       r[ Z.min lx ly ~> Z.max ux uy ].

  Definition intersection (x y : zrange) : zrange
    := let (lx, ux) := eta x in
       let (ly, uy) := eta y in
       r[ Z.max lx ly ~> Z.min ux uy ].

  Definition abs (v : zrange) : zrange
    := let (l, u) := eta v in
       r[ 0 ~> Z.max (Z.abs l) (Z.abs u) ].

  Definition two_corners (f : Z -> Z) (v : zrange) : zrange
    := let (l, u) := eta v in
       r[ Z.min (f l) (f u) ~> Z.max (f u) (f l) ].

  Definition four_corners (f : Z -> Z -> Z) (x y : zrange) : zrange
    := let (lx, ux) := eta x in
       union (two_corners (f lx) y)
             (two_corners (f ux) y).

  Definition upper_lor_land_bounds (x y : BinInt.Z) : BinInt.Z
    := 2^(1 + Z.log2_up (Z.max x y)).
  Definition extreme_lor_land_bounds (x y : zrange) : zrange
    := let mx := ZRange.upper (ZRange.abs x) in
       let my := ZRange.upper (ZRange.abs y) in
       {| lower := -upper_lor_land_bounds mx my ; upper := upper_lor_land_bounds mx my |}.
  Definition extremization_bounds (f : zrange -> zrange -> zrange) (x y : zrange) : zrange
    := let (lx, ux) := x in
       let (ly, uy) := y in
       if ((lx <? 0) || (ly <? 0))%Z%bool
       then extreme_lor_land_bounds x y
       else f x y.
  Definition land_bounds : zrange -> zrange -> zrange
    := extremization_bounds
         (fun x y
          => let (lx, ux) := x in
             let (ly, uy) := y in
             {| lower := Z.min 0 (Z.min lx ly) ; upper := Z.max 0 (Z.min ux uy) |}).

  Ltac run_tactic tac :=
    let dummy := match goal with _ => tac () end in
    I.

  Ltac is_success_run_tactic tac :=
    match goal with
    | _ => let dummy := run_tactic tac in
           true
    | _ => false
    end.
  Import Coq.FSets.FMapPositive.
  Import Coq.Lists.List.
  Import Coq.QArith.QArith_base.
  Import Crypto.Util.Option.
  Import ListNotations.
  Local Open Scope Z_scope.

  Module Export Compilers.
    Module type.
      Variant primitive := unit | Z | nat | bool.
      Inductive type := type_primitive (_:primitive) | prod (A B : type) | arrow (s d : type) | list (A : type).
      Module Export Coercions.
        Global Coercion type_primitive : primitive >-> type.
      End Coercions.

      Fixpoint interp (t : type)
        := match t with
           | unit => Datatypes.unit
           | prod A B => interp A * interp B
           | arrow A B => interp A -> interp B
           | list A => Datatypes.list (interp A)
           | nat => Datatypes.nat
           | type_primitive Z => BinInt.Z
           | bool => Datatypes.bool
           end%type.

      Fixpoint final_codomain (t : type) : type
        := match t with
           | type_primitive _ as t
           | prod _ _ as t
           | list _ as t
             => t
           | arrow s d => final_codomain d
           end.

      Fixpoint try_transport (P : type -> Type) (t1 t2 : type) : P t1 -> option (P t2)
        := match t1, t2 return P t1 -> option (P t2) with
           | unit, unit
           | Z, Z
           | nat, nat
           | bool, bool
             => @Some _
           | prod A B, prod A' B'
             => fun v
                => (v <- try_transport (fun A => P (prod A B)) A A' v;
                      try_transport (fun B => P (prod A' B)) B B' v)%option
           | arrow s d, arrow s' d'
             => fun v
                => (v <- try_transport (fun s => P (arrow s d)) s s' v;
                      try_transport (fun d => P (arrow s' d)) d d' v)%option
           | list A, list A'
             => @try_transport (fun A => P (list A)) A A'
           | unit, _
           | Z, _
           | nat, _
           | bool, _
           | prod _ _, _
           | arrow _ _, _
           | list _, _
             => fun _ => None
           end.

      Ltac reify_primitive ty :=
        lazymatch eval cbv beta in ty with
        | Datatypes.unit => unit
        | Datatypes.nat => nat
        | Datatypes.bool => bool
        | BinInt.Z => Z
        | ?ty => let dummy := match goal with
                              | _ => fail 1 "Unrecognized type:" ty
                              end in
                 constr:(I : I)
        end.

      Ltac reify ty :=
        lazymatch eval cbv beta in ty with
        | Datatypes.prod ?A ?B
          => let rA := reify A in
             let rB := reify B in
             constr:(prod rA rB)
        | ?A -> ?B
          => let rA := reify A in
             let rB := reify B in
             constr:(arrow rA rB)
        | Datatypes.list ?T
          => let rT := reify T in
             constr:(list rT)
        | type.interp ?T => T
        | _ => let rt := reify_primitive ty in
               constr:(type_primitive rt)
        end.

      Notation reify t := (ltac:(let rt := reify t in exact rt)) (only parsing).
      Notation reify_type_of e := (reify ((fun t (_ : t) => t) _ e)) (only parsing).

      Module Export Notations.
        Export Coercions.
        Delimit Scope ctype_scope with ctype.
        Bind Scope ctype_scope with type.
        Notation "()" := unit : ctype_scope.
        Notation "A * B" := (prod A B) : ctype_scope.
        Notation "A -> B" := (arrow A B) : ctype_scope.
        Notation type := type.
      End Notations.
    End type.
    Export type.Notations.

    Module Export Uncurried.
      Module Export expr.
        Inductive expr {ident : type -> type -> Type} {var : type -> Type} : type -> Type :=
        | Var {t} (v : var t) : expr t
        | TT : expr type.unit
        | AppIdent {s d} (idc : ident s d) (args : expr s) : expr d
        | App {s d} (f : expr (s -> d)) (x : expr s) : expr d
        | Pair {A B} (a : expr A) (b : expr B) : expr (A * B)
        | Abs {s d} (f : var s -> expr d) : expr (s -> d).

        Definition Expr {ident : type -> type -> Type} t := forall var, @expr ident var t.

        Definition APP {ident s d} (f : Expr (s -> d)) (x : Expr s) : Expr d
          := fun var => @App ident var s d (f var) (x var).

        Module Export Notations.
          Bind Scope expr_scope with expr.
          Delimit Scope expr_scope with expr.
          Delimit Scope Expr_scope with Expr.

          Infix "@" := App : expr_scope.
          Infix "@" := APP : Expr_scope.
          Infix "@@" := AppIdent : expr_scope.
          Notation "( x , y , .. , z )" := (Pair .. (Pair x%expr y%expr) .. z%expr) : expr_scope.
          Notation "'λ'  x .. y , t" := (Abs (fun x => .. (Abs (fun y => t%expr)) ..)) : expr_scope.
        End Notations.

        Section unexpr.
          Context {ident : type -> type -> Type}
                  {var : type -> Type}.

          Fixpoint unexpr {t} (e : @expr ident (@expr ident var) t) : @expr ident var t
            := match e in expr t return expr t with
               | Var t v => v
               | TT => TT
               | AppIdent s d idc args => AppIdent idc (unexpr args)
               | App s d f x => App (unexpr f) (unexpr x)
               | Pair A B a b => Pair (unexpr a) (unexpr b)
               | Abs s d f => Abs (fun x => unexpr (f (Var x)))
               end.
        End unexpr.

        Ltac require_primitive_const term :=
          lazymatch term with
          | S ?n => require_primitive_const n
          | O => idtac
          | true => idtac
          | false => idtac
          | tt => idtac
          | Z0 => idtac
          | Zpos ?p => require_primitive_const p
          | Zneg ?p => require_primitive_const p
          | xI ?p => require_primitive_const p
          | xO ?p => require_primitive_const p
          | xH => idtac
          | ?term => fail 0 "Not a known const:" term
          end.
        Ltac is_primitive_const term :=
          match constr:(Set) with
          | _ => let check := match goal with
                              | _ => require_primitive_const term
                              end in
                 true
          | _ => false
          end.

        Module var_context.
          Inductive list {var : type -> Type} :=
          | nil
          | cons {t} (gallina_v : type.interp t) (v : var t) (ctx : list).
        End var_context.

        Ltac type_of_first_argument_of f :=
          let f_ty := type of f in
          lazymatch eval hnf in f_ty with
          | forall x : ?T, _ => T
          end.

        Ltac require_template_parameter parameter_type :=
          first [ unify parameter_type Prop
                | unify parameter_type Set
                | unify parameter_type Type
                | lazymatch eval hnf in parameter_type with
                  | forall x : ?T, @?P x
                    => let check := constr:(fun x : T
                                            => ltac:(require_template_parameter (P x);
                                                     exact I)) in
                       idtac
                  end ].
        Ltac is_template_parameter parameter_type :=
          is_success_run_tactic ltac:(fun _ => require_template_parameter parameter_type).
        Ltac plug_template_ctx f template_ctx :=
          lazymatch template_ctx with
          | tt => f
          | (?arg, ?template_ctx')
            =>
            let T := type_of_first_argument_of f in
            let x_is_template_parameter := is_template_parameter T in
            lazymatch x_is_template_parameter with
            | true
              => plug_template_ctx (f arg) template_ctx'
            | false
              => constr:(fun x : T
                         => ltac:(let v := plug_template_ctx (f x) template_ctx in
                                  exact v))
            end
          end.

        Ltac reify_in_context ident reify_ident var term value_ctx template_ctx :=
          let reify_rec_gen term value_ctx template_ctx := reify_in_context ident reify_ident var term value_ctx template_ctx in
          let reify_rec term := reify_rec_gen term value_ctx template_ctx in
          let reify_rec_not_head term := reify_rec_gen term value_ctx tt in
          let mkAppIdent idc args
              := let rargs := reify_rec_not_head args in
                 constr:(@AppIdent ident var _ _ idc rargs) in
          let do_reify_ident term else_tac
              := let term_is_primitive_const := is_primitive_const term in
                 reify_ident
                   mkAppIdent
                   term_is_primitive_const
                   term
                   else_tac in

          lazymatch value_ctx with
          | context[@var_context.cons _ ?rT term ?v _]
            => constr:(@Var ident var rT v)
          | _
            =>
            lazymatch term with
            | match ?b with true => ?t | false => ?f end
              => let T := type of t in
                 reify_rec (@bool_rect (fun _ => T) t f b)
            | match ?x with Datatypes.pair a b => ?f end
              => reify_rec (match Datatypes.fst x, Datatypes.snd x return _ with
                            | a, b => f
                            end)
            | match ?x with nil => ?N | cons a b => @?C a b end
              => let T := type of term in
                 reify_rec (@list_case _ (fun _ => T) N C x)
            | let x := ?a in @?b x
              => let A := type of a in
                 let B := lazymatch type of b with forall x, @?B x => B end in
                 reify_rec (b a)
            | Datatypes.pair ?x ?y
              => let rx := reify_rec x in
                 let ry := reify_rec y in
                 constr:(Pair (ident:=ident) (var:=var) rx ry)
            | tt
              => constr:(@TT ident var)
            | (fun x : ?T => ?f)
              =>
              let x_is_template_parameter := is_template_parameter T in
              lazymatch x_is_template_parameter with
              | true
                =>
                lazymatch template_ctx with
                | (?arg, ?template_ctx)
                  =>
                  lazymatch type of term with
                  | forall y, ?P
                    => reify_rec_gen (match arg as y return P with x => f end) value_ctx template_ctx
                  end
                end
              | false
                =>
                let rT := type.reify T in
                let not_x := fresh in
                let not_x2 := fresh in
                let not_x3 := fresh in

                let rf0 :=
                    constr:(
                      fun (x : T) (not_x : var rT)
                      => match f, @var_context.cons var rT x not_x value_ctx return _ with
                         | not_x2, not_x3
                           => ltac:(
                                let f := (eval cbv delta [not_x2] in not_x2) in
                                let var_ctx := (eval cbv delta [not_x3] in not_x3) in

                                let rf := reify_rec_gen f var_ctx template_ctx in
                                exact rf)
                         end) in
                lazymatch rf0 with
                | (fun _ => ?rf)
                  => constr:(@Abs ident var rT _ rf)
                | _
                  =>
                  let dummy := match goal with
                               | _ => fail 1 "Failure to eliminate functional dependencies of" rf0
                               end in
                  constr:(I : I)
                end
              end
            | _
              =>
              do_reify_ident
                term
                ltac:(
                fun _
                =>
                  lazymatch term with
                  | ?f ?x
                    =>
                    let ty := type_of_first_argument_of f in
                    let x_is_template_parameter := is_template_parameter ty in
                    lazymatch x_is_template_parameter with
                    | true
                      =>
                      reify_rec_gen f value_ctx (x, template_ctx)
                    | false
                      => let rx := reify_rec_gen x value_ctx tt in
                         let rf := reify_rec_gen f value_ctx template_ctx in
                         constr:(App (ident:=ident) (var:=var) rf rx)
                    end
                  | _
                    => let term' := plug_template_ctx term template_ctx in
                       do_reify_ident
                         term'
                         ltac:(fun _
                               =>

                                 let term
                                     := match constr:(Set) with
                                        | _ => (eval cbv delta [term] in term)
                                        | _
                                          => let dummy := match goal with
                                                          | _ => fail 2 "Unrecognized term:" term'
                                                          end in
                                             constr:(I : I)
                                        end in
                                 reify_rec term)
                  end)
            end
          end.
        Ltac reify ident reify_ident var term :=
          reify_in_context ident reify_ident var term (@var_context.nil var) tt.
        Ltac Reify ident reify_ident term :=
          constr:(fun var : type -> Type
                  => ltac:(let r := reify ident reify_ident var term in
                           exact r)).

        Module for_reification.
          Module Export ident.
            Import type.
            Inductive ident : type -> type -> Set :=
            | primitive {t:type.primitive} (v : interp t) : ident () t
            | Let_In {tx tC} : ident (tx * (tx -> tC)) tC
            | Nat_succ : ident nat nat
            | Nat_max : ident (nat * nat) nat
            | Nat_mul : ident (nat * nat) nat
            | Nat_add : ident (nat * nat) nat
            | Nat_sub : ident (nat * nat) nat
            | nil {t} : ident () (list t)
            | cons {t} : ident (t * list t) (list t)
            | fst {A B} : ident (A * B) A
            | snd {A B} : ident (A * B) B
            | bool_rect {T} : ident ((unit -> T) * (unit -> T) * bool) T
            | nat_rect {P} : ident ((unit -> P) * (nat * P -> P) * nat) P
            | list_rect {A P} : ident ((unit -> P) * (A * list A * P -> P) * list A) P
            | list_case {A P} : ident ((unit -> P) * (A * list A -> P) * list A) P
            | pred : ident nat nat
            | List_length {T} : ident (list T) nat
            | List_seq : ident (nat * nat) (list nat)
            | List_repeat {A} : ident (A * nat) (list A)
            | List_combine {A B} : ident (list A * list B) (list (A * B))
            | List_map {A B} : ident ((A -> B) * list A) (list B)
            | List_flat_map {A B} : ident ((A -> list B) * list A) (list B)
            | List_partition {A} : ident ((A -> bool) * list A) (list A * list A)
            | List_app {A} : ident (list A * list A) (list A)
            | List_rev {A} : ident (list A) (list A)
            | List_fold_right {A B} : ident ((B * A -> A) * A * list B) A
            | List_update_nth {T} : ident (nat * (T -> T) * list T) (list T)
            | List_nth_default {T} : ident (T * list T * nat) T
            | Z_add : ident (Z * Z) Z
            | Z_mul : ident (Z * Z) Z
            | Z_pow : ident (Z * Z) Z
            | Z_sub : ident (Z * Z) Z
            | Z_opp : ident Z Z
            | Z_div : ident (Z * Z) Z
            | Z_modulo : ident (Z * Z) Z
            | Z_eqb : ident (Z * Z) bool
            | Z_leb : ident (Z * Z) bool
            | Z_of_nat : ident nat Z
            .

            Ltac reify
                 mkAppIdent
                 term_is_primitive_const
                 term
                 else_tac :=

              lazymatch term with
              | Nat.succ ?x => mkAppIdent Nat_succ x
              | Nat.add ?x ?y => mkAppIdent Nat_add (x, y)
              | Nat.sub ?x ?y => mkAppIdent Nat_sub (x, y)
              | Nat.mul ?x ?y => mkAppIdent Nat_mul (x, y)
              | Nat.max ?x ?y => mkAppIdent Nat_max (x, y)
              | S ?x => mkAppIdent Nat_succ x
              | @Datatypes.nil ?T
                => let rT := type.reify T in
                   mkAppIdent (@ident.nil rT) tt
              | @Datatypes.cons ?T ?x ?xs
                => let rT := type.reify T in
                   mkAppIdent (@ident.cons rT) (x, xs)
              | @Datatypes.fst ?A ?B ?x
                => let rA := type.reify A in
                   let rB := type.reify B in
                   mkAppIdent (@ident.fst rA rB) x
              | @Datatypes.snd ?A ?B ?x
                => let rA := type.reify A in
                   let rB := type.reify B in
                   mkAppIdent (@ident.snd rA rB) x
              | @Datatypes.bool_rect (fun _ => ?T) ?Ptrue ?Pfalse ?b
                => let rT := type.reify T in
                   mkAppIdent (@ident.bool_rect rT)
                              ((fun _ : Datatypes.unit => Ptrue), (fun _ : Datatypes.unit => Pfalse), b)
              | @Datatypes.nat_rect (fun _ => ?T) ?P0 (fun (n' : Datatypes.nat) Pn => ?PS) ?n
                => let rT := type.reify T in
                   let pat := fresh "pat" in
                   mkAppIdent (@ident.nat_rect rT) ((fun _ : Datatypes.unit => P0),
                                                    (fun pat : Datatypes.nat * T
                                                     => let '(n', Pn) := pat in PS),
                                                    n)
              | @Datatypes.nat_rect (fun _ => ?T) ?P0 ?PS ?n
                => let dummy := match goal with _ => fail 1 "nat_rect successor case is not syntactically a function of two arguments:" PS end in
                   constr:(I : I)
              | @Datatypes.list_rect ?A (fun _ => ?T) ?Pnil (fun a tl Ptl => ?PS) ?ls
                => let rA := type.reify A in
                   let rT := type.reify T in
                   let pat := fresh "pat" in
                   mkAppIdent (@ident.list_rect rA rT)
                              ((fun _ : Datatypes.unit => Pnil),
                               (fun pat : A * Datatypes.list A * T
                                => let '(a, tl, Ptl) := pat in PS),
                               ls)
              | @Datatypes.list_rect ?A (fun _ => ?T) ?Pnil ?PS ?ls
                => let dummy := match goal with _ => fail 1 "list_rect successor case is not syntactically a function of three arguments:" PS end in
                   constr:(I : I)
              | @ListUtil.list_case ?A (fun _ => ?T) ?Pnil (fun a tl => ?PS) ?ls
                => let rA := type.reify A in
                   let rT := type.reify T in
                   let pat := fresh "pat" in
                   mkAppIdent (@ident.list_case rA rT)
                              ((fun _ : Datatypes.unit => Pnil),
                               (fun pat : A * Datatypes.list A
                                => let '(a, tl) := pat in PS),
                               ls)
              | @ListUtil.list_case ?A (fun _ => ?T) ?Pnil ?PS ?ls
                => let dummy := match goal with _ => fail 1 "list_case successor case is not syntactically a function of two arguments:" PS end in
                   constr:(I : I)
              | Nat.pred ?x => mkAppIdent ident.pred x
              | @List.length ?A ?x =>
                let rA := type.reify A in
                mkAppIdent (@ident.List_length rA) x
              | List.seq ?x ?y  => mkAppIdent ident.List_seq (x, y)
              | @List.repeat ?A ?x ?y
                => let rA := type.reify A in
                   mkAppIdent (@ident.List_repeat rA) (x, y)
              | @LetIn.Let_In ?A (fun _ => ?B) ?x ?f
                => let rA := type.reify A in
                   let rB := type.reify B in
                   mkAppIdent (@ident.Let_In rA rB) (x, f)
              | @LetIn.Let_In ?A ?B ?x ?f
                => let dummy := match goal with _ => fail 1 "Let_In contains a dependent type λ as its second argument:" B end in
                   constr:(I : I)
              | @combine ?A ?B ?ls1 ?ls2
                => let rA := type.reify A in
                   let rB := type.reify B in
                   mkAppIdent (@ident.List_combine rA rB) (ls1, ls2)
              | @List.map ?A ?B ?f ?ls
                => let rA := type.reify A in
                   let rB := type.reify B in
                   mkAppIdent (@ident.List_map rA rB) (f, ls)
              | @List.flat_map ?A ?B ?f ?ls
                => let rA := type.reify A in
                   let rB := type.reify B in
                   mkAppIdent (@ident.List_flat_map rA rB) (f, ls)
              | @List.partition ?A ?f ?ls
                => let rA := type.reify A in
                   mkAppIdent (@ident.List_partition rA) (f, ls)
              | @List.app ?A ?ls1 ?ls2
                => let rA := type.reify A in
                   mkAppIdent (@ident.List_app rA) (ls1, ls2)
              | @List.rev ?A ?ls
                => let rA := type.reify A in
                   mkAppIdent (@ident.List_rev rA) ls
              | @List.fold_right ?A ?B (fun b a => ?f) ?a0 ?ls
                => let rA := type.reify A in
                   let rB := type.reify B in
                   let pat := fresh "pat" in
                   mkAppIdent (@ident.List_fold_right rA rB) ((fun pat : B * A => let '(b, a) := pat in f), a0, ls)
              | @List.fold_right ?A ?B ?f ?a0 ?ls
                => let dummy := match goal with _ => fail 1 "List.fold_right function argument is not syntactically a function of two arguments:" f end in
                   constr:(I : I)
              | @update_nth ?T ?n ?f ?ls
                => let rT := type.reify T in
                   mkAppIdent (@ident.List_update_nth rT) (n, f, ls)
              | @List.nth_default ?T ?d ?ls ?n
                => let rT := type.reify T in
                   mkAppIdent (@ident.List_nth_default rT) (d, ls, n)
              | Z.add ?x ?y => mkAppIdent ident.Z_add (x, y)
              | Z.mul ?x ?y => mkAppIdent ident.Z_mul (x, y)
              | Z.pow ?x ?y => mkAppIdent ident.Z_pow (x, y)
              | Z.sub ?x ?y => mkAppIdent ident.Z_sub (x, y)
              | Z.opp ?x => mkAppIdent ident.Z_opp x
              | Z.div ?x ?y => mkAppIdent ident.Z_div (x, y)
              | Z.modulo ?x ?y => mkAppIdent ident.Z_modulo (x, y)
              | Z.eqb ?x ?y => mkAppIdent ident.Z_eqb (x, y)
              | Z.leb ?x ?y => mkAppIdent ident.Z_leb (x, y)
              | Z.of_nat ?x => mkAppIdent ident.Z_of_nat x
              | _
                => lazymatch term_is_primitive_const with
                   | true
                     =>
                     let assert_const := match goal with
                                         | _ => require_primitive_const term
                                         end in
                     let T := type of term in
                     let rT := type.reify_primitive T in
                     mkAppIdent (@ident.primitive rT term) tt
                   | false => else_tac ()
                   end
              end.

            Module Export Notations.
              Notation ident := ident.
            End Notations.
          End ident.

          Module Export Notations.
            Include ident.Notations.
            Notation expr := (@expr ident).
            Notation Expr := (@Expr ident).

            Module Export Reification.
              Ltac Reify term := expr.Reify ident ident.reify term.
            End Reification.
          End Notations.
          Include Notations.
        End for_reification.

        Module Export default.
          Module ident.
            Import type.
            Inductive ident : type -> type -> Set :=
            | primitive {t : type.primitive} (v : interp t) : ident () t
            | Let_In {tx tC} : ident (tx * (tx -> tC)) tC
            | Nat_succ : ident nat nat
            | Nat_add : ident (nat * nat) nat
            | Nat_sub : ident (nat * nat) nat
            | Nat_mul : ident (nat * nat) nat
            | Nat_max : ident (nat * nat) nat
            | nil {t} : ident () (list t)
            | cons {t} : ident (t * list t) (list t)
            | fst {A B} : ident (A * B) A
            | snd {A B} : ident (A * B) B
            | bool_rect {T} : ident ((unit -> T) * (unit -> T) * bool) T
            | nat_rect {P} : ident ((unit -> P) * (nat * P -> P) * nat) P
            | pred : ident nat nat
            | list_rect {A P} : ident ((unit -> P) * (A * list A * P -> P) * list A) P
            | List_nth_default {T} : ident (T * list T * nat) T
            | List_nth_default_concrete {T : type.primitive} (d : interp T) (n : Datatypes.nat) : ident (list T) T
            | Z_shiftr (offset : BinInt.Z) : ident Z Z
            | Z_shiftl (offset : BinInt.Z) : ident Z Z
            | Z_land (mask : BinInt.Z) : ident Z Z
            | Z_add : ident (Z * Z) Z
            | Z_mul : ident (Z * Z) Z
            | Z_pow : ident (Z * Z) Z
            | Z_sub : ident (Z * Z) Z
            | Z_opp : ident Z Z
            | Z_div : ident (Z * Z) Z
            | Z_modulo : ident (Z * Z) Z
            | Z_eqb : ident (Z * Z) bool
            | Z_leb : ident (Z * Z) bool
            | Z_of_nat : ident nat Z
            | Z_cast (range : zrange) : ident Z Z
            | Z_cast2 (range : zrange * zrange) : ident (Z * Z) (Z * Z)
            .

            Notation curry0 f
              := (fun 'tt => f).
            Notation curry2 f
              := (fun '(a, b) => f a b).
            Notation curry3 f
              := (fun '(a, b, c) => f a b c).
            Notation uncurry2 f
              := (fun a b => f (a, b)).
            Notation uncurry3 f
              := (fun a b c => f (a, b, c)).
            Notation curry3_23 f
              := (fun '(a, b, c) => f a (uncurry3 b) c).
            Notation curry3_2 f
              := (fun '(a, b, c) => f a (uncurry2 b) c).

            Section gen.
              Context (cast_outside_of_range : zrange -> BinInt.Z -> BinInt.Z).

              Definition cast (r : zrange) (x : BinInt.Z)
                := if (lower r <=? x) && (x <=? upper r)
                   then x
                   else cast_outside_of_range r x.

              Definition gen_interp {s d} (idc : ident s d) : type.interp s -> type.interp d
                := match idc in ident s d return type.interp s -> type.interp d with
                   | primitive _ v => curry0 v
                   | Let_In tx tC => curry2 (@LetIn.Let_In (type.interp tx) (fun _ => type.interp tC))
                   | Nat_succ => Nat.succ
                   | Nat_add => curry2 Nat.add
                   | Nat_sub => curry2 Nat.sub
                   | Nat_mul => curry2 Nat.mul
                   | Nat_max => curry2 Nat.max
                   | nil t => curry0 (@Datatypes.nil (type.interp t))
                   | cons t => curry2 (@Datatypes.cons (type.interp t))
                   | fst A B => @Datatypes.fst (type.interp A) (type.interp B)
                   | snd A B => @Datatypes.snd (type.interp A) (type.interp B)
                   | bool_rect T => curry3 (fun t f => @Datatypes.bool_rect (fun _ => type.interp T) (t tt) (f tt))
                   | nat_rect P => curry3_2 (fun O_case => @Datatypes.nat_rect (fun _ => type.interp P) (O_case tt))
                   | pred => Nat.pred
                   | list_rect A P => curry3_23 (fun N_case => @Datatypes.list_rect (type.interp A) (fun _ => type.interp P) (N_case tt))
                   | List_nth_default T => curry3 (@List.nth_default (type.interp T))
                   | List_nth_default_concrete T d n => fun ls => @List.nth_default (type.interp T) d ls n
                   | Z_shiftr n => fun v => Z.shiftr v n
                   | Z_shiftl n => fun v => Z.shiftl v n
                   | Z_land mask => fun v => Z.land v mask
                   | Z_add => curry2 Z.add
                   | Z_mul => curry2 Z.mul
                   | Z_pow => curry2 Z.pow
                   | Z_modulo => curry2 Z.modulo
                   | Z_sub => curry2 Z.sub
                   | Z_opp => Z.opp
                   | Z_div => curry2 Z.div
                   | Z_eqb => curry2 Z.eqb
                   | Z_leb => curry2 Z.leb
                   | Z_of_nat => Z.of_nat
                   | Z_cast r => cast r
                   | Z_cast2 (r1, r2) => fun '(x1, x2) => (cast r1 x1, cast r2 x2)
                   end.
            End gen.

            Definition cast_outside_of_range (r : zrange) (v : BinInt.Z) : BinInt.Z.
              exact v.
            Qed.

            Definition interp {s d} (idc : ident s d) : type.interp s -> type.interp d
              := @gen_interp cast_outside_of_range s d idc.

            Ltac reify
                 mkAppIdent
                 term_is_primitive_const
                 term
                 else_tac :=

              lazymatch term with
              | Nat.succ ?x => mkAppIdent Nat_succ x
              | Nat.add ?x ?y => mkAppIdent Nat_add (x, y)
              | Nat.sub ?x ?y => mkAppIdent Nat_sub (x, y)
              | Nat.mul ?x ?y => mkAppIdent Nat_mul (x, y)
              | Nat.max ?x ?y => mkAppIdent Nat_max (x, y)
              | S ?x => mkAppIdent Nat_succ x
              | @Datatypes.nil ?T
                => let rT := type.reify T in
                   mkAppIdent (@ident.nil rT) tt
              | @Datatypes.cons ?T ?x ?xs
                => let rT := type.reify T in
                   mkAppIdent (@ident.cons rT) (x, xs)
              | @Datatypes.fst ?A ?B ?x
                => let rA := type.reify A in
                   let rB := type.reify B in
                   mkAppIdent (@ident.fst rA rB) x
              | @Datatypes.snd ?A ?B ?x
                => let rA := type.reify A in
                   let rB := type.reify B in
                   mkAppIdent (@ident.snd rA rB) x
              | @Datatypes.bool_rect (fun _ => ?T) ?Ptrue ?Pfalse ?b
                => let rT := type.reify T in
                   mkAppIdent (@ident.bool_rect rT)
                              ((fun _ : Datatypes.unit => Ptrue), (fun _ : Datatypes.unit => Pfalse), b)
              | @Datatypes.nat_rect (fun _ => ?T) ?P0 (fun (n' : Datatypes.nat) Pn => ?PS) ?n
                => let rT := type.reify T in
                   let pat := fresh "pat" in
                   mkAppIdent (@ident.nat_rect rT)
                              ((fun _ : Datatypes.unit => P0),
                               (fun pat : Datatypes.nat * T
                                => let '(n', Pn) := pat in PS),
                               n)
              | @Datatypes.nat_rect (fun _ => ?T) ?P0 ?PS ?n
                => let dummy := match goal with _ => fail 1 "nat_rect successor case is not syntactically a function of two arguments:" PS end in
                   constr:(I : I)
              | Nat.pred ?x => mkAppIdent ident.pred x
              | @LetIn.Let_In ?A (fun _ => ?B) ?x ?f
                => let rA := type.reify A in
                   let rB := type.reify B in
                   mkAppIdent (@ident.Let_In rA rB) (x, f)
              | @LetIn.Let_In ?A ?B ?x ?f
                => let dummy := match goal with _ => fail 1 "Let_In contains a dependent type λ as its second argument:" B end in
                   constr:(I : I)
              | @Datatypes.list_rect ?A (fun _ => ?B) ?Pnil (fun x xs rec => ?Pcons) ?ls
                => let rA := type.reify A in
                   let rB := type.reify B in
                   let pat := fresh "pat" in
                   let pat' := fresh "pat" in
                   mkAppIdent (@ident.list_rect rA rB)
                              ((fun _ : Datatypes.unit => Pnil),
                               (fun pat : A * Datatypes.list A * B
                                => let '(pat', rec) := pat in
                                   let '(x, xs) := pat' in
                                   Pcons),
                               ls)
              | @Datatypes.list_rect ?A (fun _ => ?B) ?Pnil ?Pcons ?ls
                => let dummy := match goal with _ => fail 1 "list_rect cons case is not syntactically a function of three arguments:" Pcons end in
                   constr:(I : I)
              | @List.nth_default ?T ?d ?ls ?n
                => let rT := type.reify T in
                   mkAppIdent (@ident.List_nth_default rT) (d, ls, n)
              | Z.add ?x ?y => mkAppIdent ident.Z_add (x, y)
              | Z.mul ?x ?y => mkAppIdent ident.Z_mul (x, y)
              | Z.pow ?x ?y => mkAppIdent ident.Z_pow (x, y)
              | Z.sub ?x ?y => mkAppIdent ident.Z_sub (x, y)
              | Z.opp ?x => mkAppIdent ident.Z_opp x
              | Z.div ?x ?y => mkAppIdent ident.Z_div (x, y)
              | Z.modulo ?x ?y => mkAppIdent ident.Z_modulo (x, y)
              | Z.eqb ?x ?y => mkAppIdent ident.Z_eqb (x, y)
              | Z.leb ?x ?y => mkAppIdent ident.Z_leb (x, y)
              | Z.of_nat ?x => mkAppIdent ident.Z_of_nat x
              | _
                => lazymatch term_is_primitive_const with
                   | true
                     =>
                     let assert_const := match goal with
                                         | _ => require_primitive_const term
                                         end in
                     let T := type of term in
                     let rT := type.reify_primitive T in
                     mkAppIdent (@ident.primitive rT term) tt
                   | _ => else_tac ()
                   end
              end.

            Module Export List.
              Notation nth_default := List_nth_default.
              Notation nth_default_concrete := List_nth_default_concrete.
            End List.

            Module Export Z.
              Notation shiftr := Z_shiftr.
              Notation shiftl := Z_shiftl.
              Notation land := Z_land.
              Notation add := Z_add.
              Notation mul := Z_mul.
              Notation pow := Z_pow.
              Notation sub := Z_sub.
              Notation opp := Z_opp.
              Notation div := Z_div.
              Notation modulo := Z_modulo.
              Notation eqb := Z_eqb.
              Notation leb := Z_leb.
              Notation of_nat := Z_of_nat.
              Notation cast := Z_cast.
              Notation cast2 := Z_cast2.
            End Z.

            Module Export Notations.
              Notation ident := ident.
            End Notations.
          End ident.

          Module Export Notations.
            Include ident.Notations.
            Notation expr := (@expr ident).
            Notation Expr := (@Expr ident).

            Notation "'expr_let' x := A 'in' b" := (AppIdent ident.Let_In (Pair A%expr (Abs (fun x => b%expr)))) : expr_scope.

            Ltac reify var term := expr.reify ident ident.reify var term.
          End Notations.
          Include Notations.
        End default.
      End expr.

      Module Export canonicalize_list_recursion.
        Module Export ident.
          Local Ltac app_and_maybe_cancel term :=
            lazymatch term with
            | Abs (fun x : @expr ?var ?T => ?f)
              => eval cbv [unexpr] in (fun x : @expr var T => @unexpr ident.ident var _ f)
            | Abs (fun x : ?T => ?f)
              => let dummy := match goal with _ => fail 1 "Invalid var type:" T end in
                 constr:(I : I)
            end.

          Definition transfer {var} {s d} (idc : for_reification.ident s d) : @expr var s -> @expr var d
            := let List_app A :=
                   list_rect
                     (fun _ => list (type.interp A) -> list (type.interp A))
                     (fun m => m)
                     (fun a l1 app_l1 m => a :: app_l1 m) in
               match idc in for_reification.ident s d return @expr var s -> @expr var d with
               | for_reification.ident.Let_In tx tC
                 => AppIdent ident.Let_In
               | for_reification.ident.Nat_succ
                 => AppIdent ident.Nat_succ
               | for_reification.ident.Nat_add
                 => AppIdent ident.Nat_add
               | for_reification.ident.Nat_sub
                 => AppIdent ident.Nat_sub
               | for_reification.ident.Nat_mul
                 => AppIdent ident.Nat_mul
               | for_reification.ident.Nat_max
                 => AppIdent ident.Nat_max
               | for_reification.ident.nil t
                 => AppIdent ident.nil
               | for_reification.ident.cons t
                 => AppIdent ident.cons
               | for_reification.ident.fst A B
                 => AppIdent ident.fst
               | for_reification.ident.snd A B
                 => AppIdent ident.snd
               | for_reification.ident.bool_rect T
                 => AppIdent ident.bool_rect
               | for_reification.ident.nat_rect P
                 => AppIdent ident.nat_rect
               | for_reification.ident.list_rect A P
                 => AppIdent ident.list_rect
               | for_reification.ident.pred
                 => AppIdent ident.pred
               | for_reification.ident.primitive t v
                 => AppIdent (ident.primitive v)
               | for_reification.ident.Z_add
                 => AppIdent ident.Z.add
               | for_reification.ident.Z_mul
                 => AppIdent ident.Z.mul
               | for_reification.ident.Z_pow
                 => AppIdent ident.Z.pow
               | for_reification.ident.Z_sub
                 => AppIdent ident.Z.sub
               | for_reification.ident.Z_opp
                 => AppIdent ident.Z.opp
               | for_reification.ident.Z_div
                 => AppIdent ident.Z.div
               | for_reification.ident.Z_modulo
                 => AppIdent ident.Z.modulo
               | for_reification.ident.Z_eqb
                 => AppIdent ident.Z.eqb
               | for_reification.ident.Z_leb
                 => AppIdent ident.Z.leb
               | for_reification.ident.Z_of_nat
                 => AppIdent ident.Z.of_nat
               | for_reification.ident.list_case A P
                 => ltac:(
                      let v := reify
                                 (@expr var)
                                 (fun '((Pnil, Pcons, ls)
                                        : (unit -> type.interp P)
                                          * (type.interp A * list (type.interp A) -> type.interp P)
                                          * (list (type.interp A)))
                                  => list_rect
                                       (fun _ => type.interp P)
                                       (Pnil tt)
                                       (fun x xs _ => Pcons (x, xs))
                                       ls) in
                      let v := app_and_maybe_cancel v in exact v)
               | for_reification.ident.List_length A
                 => ltac:(
                      let v := reify
                                 (@expr var)
                                 (fun (ls : list (type.interp A))
                                  => list_rect
                                       (fun _ => nat)
                                       0%nat
                                       (fun a t len_t => S len_t)
                                       ls) in
                      let v := app_and_maybe_cancel v in exact v)
               | for_reification.ident.List_seq
                 => ltac:(
                      let v
                          :=
                          reify
                            (@expr var)
                            (fun start_len : nat * nat
                             => nat_rect
                                  (fun _ => nat -> list nat)
                                  (fun _ => nil)
                                  (fun len seq_len start => cons start (seq_len (S start)))
                                  (snd start_len) (fst start_len)) in
                      let v := app_and_maybe_cancel v in exact v)
               | for_reification.ident.List_repeat A
                 => ltac:(
                      let v := reify
                                 (@expr var)
                                 (fun (xn : type.interp A * nat)
                                  => nat_rect
                                       (fun _ => list (type.interp A))
                                       nil
                                       (fun k repeat_k => cons (fst xn) repeat_k)
                                       (snd xn)) in
                      let v := app_and_maybe_cancel v in exact v)
               | for_reification.ident.List_combine A B
                 => ltac:(
                      let v := reify
                                 (@expr var)
                                 (fun '((ls1, ls2) : list (type.interp A) * list (type.interp B))
                                  => list_rect
                                       (fun _ => list (type.interp B) -> list (type.interp A * type.interp B))
                                       (fun l' => nil)
                                       (fun x tl combine_tl rest
                                        => list_rect
                                             (fun _ => list (type.interp A * type.interp B))
                                             nil
                                             (fun y tl' _
                                              => (x, y) :: combine_tl tl')
                                             rest)
                                       ls1
                                       ls2) in
                      let v := app_and_maybe_cancel v in exact v)
               | for_reification.ident.List_map A B
                 => ltac:(
                      let v := reify
                                 (@expr var)
                                 (fun '((f, ls) : (type.interp A -> type.interp B) * Datatypes.list (type.interp A))
                                  => list_rect
                                       (fun _ => list (type.interp B))
                                       nil
                                       (fun a t map_t => f a :: map_t)
                                       ls) in
                      let v := app_and_maybe_cancel v in exact v)
               | for_reification.ident.List_flat_map A B
                 => ltac:(
                      let List_app := (eval cbv [List_app] in (List_app B)) in
                      let v := reify
                                 (@expr var)
                                 (fun '((f, ls) : (type.interp A -> list (type.interp B)) * list (type.interp A))
                                  => list_rect
                                       (fun _ => list (type.interp B))
                                       nil
                                       (fun x t flat_map_t => List_app (f x) flat_map_t)
                                       ls) in
                      let v := app_and_maybe_cancel v in exact v)
               | for_reification.ident.List_partition A
                 => ltac:(
                      let v := reify
                                 (@expr var)
                                 (fun '((f, ls) : (type.interp A -> bool) * list (type.interp A))
                                  => list_rect
                                       (fun _ => list (type.interp A) * list (type.interp A))%type
                                       (nil, nil)
                                       (fun x tl partition_tl
                                        => let g := fst partition_tl in
                                           let d := snd partition_tl in
                                           if f x then (x :: g, d) else (g, x :: d))
                                       ls) in
                      let v := app_and_maybe_cancel v in exact v)
               | for_reification.ident.List_app A
                 => ltac:(
                      let List_app := (eval cbv [List_app] in (List_app A)) in
                      let v := reify (@expr var) (fun '(ls1, ls2) => List_app ls1 ls2) in
                      let v := app_and_maybe_cancel v in exact v)
               | for_reification.ident.List_rev A
                 => ltac:(
                      let List_app := (eval cbv [List_app] in (List_app A)) in
                      let v := reify
                                 (@expr var)
                                 (fun ls
                                  => list_rect
                                       (fun _ => list (type.interp A))
                                       nil
                                       (fun x l' rev_l' => List_app rev_l' [x])
                                       ls) in
                      let v := app_and_maybe_cancel v in exact v)
               | for_reification.ident.List_fold_right A B
                 => ltac:(
                      let v := reify
                                 (@expr var)
                                 (fun '((f, a0, ls)
                                        : (type.interp B * type.interp A -> type.interp A) * type.interp A * list (type.interp B))
                                  => list_rect
                                       (fun _ => type.interp A)
                                       a0
                                       (fun b t fold_right_t => f (b, fold_right_t))
                                       ls) in
                      let v := app_and_maybe_cancel v in exact v)
               | for_reification.ident.List_update_nth T
                 => ltac:(
                      let v := reify
                                 (@expr var)
                                 (fun '((n, f, ls) : nat * (type.interp T -> type.interp T) * list (type.interp T))
                                  => nat_rect
                                       (fun _ => list (type.interp T) -> list (type.interp T))
                                       (fun ls
                                        => list_rect
                                             (fun _ => list (type.interp T))
                                             nil
                                             (fun x' xs' __ => f x' :: xs')
                                             ls)
                                       (fun n' update_nth_n' ls
                                        => list_rect
                                             (fun _ => list (type.interp T))
                                             nil
                                             (fun x' xs' __ => x' :: update_nth_n' xs')
                                             ls)
                                       n
                                       ls) in
                      let v := app_and_maybe_cancel v in exact v)
               | for_reification.ident.List_nth_default T
                 => AppIdent ident.List_nth_default

               end%expr.
        End ident.

        Module Export expr.
          Section with_var.
            Context {var : type -> Type}.

            Fixpoint transfer {t} (e : @for_reification.Notations.expr var t)
              : @expr var t
              := match e  with
                 | Var t v => Var v
                 | TT => TT
                 | Pair A B a b => Pair (@transfer A a) (@transfer B b)
                 | AppIdent s d idc args => @ident.transfer var s d idc (@transfer _ args)
                 | App s d f x => App (@transfer _ f) (@transfer _ x)
                 | Abs s d f => Abs (fun x => @transfer d (f x))
                 end.
          End with_var.

          Definition Transfer {t} (e : for_reification.Notations.Expr t) : Expr t
            := fun var => transfer (e _).
          Notation canonicalize_list_recursion := canonicalize_list_recursion.expr.Transfer.
          Section invert.
            Context {var : type -> Type}.

            Local Notation if_arrow f
              := (fun t => match t return Type with
                           | type.arrow s d => f s d
                           | _ => True
                           end) (only parsing).
            Local Notation if_prod f
              := (fun t => match t return Type with
                           | type.prod A B => f A B
                           | _ => True
                           end).

            Definition invert_Abs {s d} (e : @expr var (type.arrow s d)) : option (var s -> @expr var d)
              := match e in expr.expr t return option (if_arrow (fun _ _ => _) t) with
                 | Abs s d f => Some f
                 | _ => None
                 end.

            Definition invert_AppIdent {d} (e : @expr var d) : option { s : _ & @ident s d * @expr var s }%type
              := match e with
                 | AppIdent s d idc args
                   => Some (existT _ s (idc, args))
                 | _ => None
                 end.

            Definition invert_Pair {A B} (e : @expr var (type.prod A B)) : option (@expr var A * @expr var B)
              := match e in expr.expr t return option (if_prod (fun A B => expr A * expr B)%type t) with
                 | Pair A B a b
                   => Some (a, b)
                 | _ => None
                 end.
            Definition reflect_primitive {t} (e : @expr var (type.type_primitive t)) : option (type.interp (type.type_primitive t))
              := match invert_AppIdent e with
                 | Some (existT s (idc, args))
                   => match idc in ident _ t return option (type.interp t) with
                      | ident.primitive _ v => Some v
                      | _ => None
                      end
                 | None => None
                 end.
            Definition invert_Z_opp (e : @expr var type.Z) : option (@expr var type.Z)
              := match invert_AppIdent e with
                 | Some (existT s (idc, args))
                   => match idc in ident s t return expr s -> option (expr type.Z) with
                      | ident.Z_opp => fun v => Some v
                      | _ => fun _ => None
                      end args
                 | None => None
                 end.

            Definition invert_Z_cast (e : @expr var type.Z) : option (zrange * @expr var type.Z)
              := match invert_AppIdent e with
                 | Some (existT s (idc, args))
                   => match idc in ident s t return expr s -> option (zrange * expr type.Z) with
                      | ident.Z_cast r => fun v => Some (r, v)
                      | _ => fun _ => None
                      end args
                 | None => None
                 end.

            Definition invert_Z_cast2 (e : @expr var (type.Z * type.Z)) : option ((zrange * zrange) * @expr var (type.Z * type.Z))
              := match invert_AppIdent e with
                 | Some (existT s (idc, args))
                   => match idc in ident s t return expr s -> option ((zrange * zrange) * expr (type.Z * type.Z)) with
                      | ident.Z_cast2 r => fun v => Some (r, v)
                      | _ => fun _ => None
                      end args
                 | None => None
                 end.

            Local Notation list_expr
              := (fun t => match t return Type with
                           | type.list T => list (expr T)
                           | _ => True
                           end) (only parsing).

            Fixpoint reflect_list {t} (e : @expr var (type.list t))
              : option (list (@expr var t))
              := match e in expr.expr t return option (list_expr t) with
                 | AppIdent s (type.list t) idc x_xs
                   => match x_xs in expr.expr s return ident s (type.list t) -> option (list (expr t)) with
                      | Pair A (type.list B) x xs
                        => match @reflect_list B xs with
                           | Some xs
                             => fun idc
                                => match idc in ident s d
                                         return if_prod (fun A B => expr A) s
                                                -> if_prod (fun A B => list_expr B) s
                                                -> option (list_expr d)
                                   with
                                   | ident.cons A
                                     => fun x xs => Some (cons x xs)
                                   | _ => fun _ _ => None
                                   end x xs
                           | None => fun _ => None
                           end
                      | _
                        => fun idc
                           => match idc in ident _ t return option (list_expr t) with
                              | ident.nil _ => Some nil
                              | _ => None
                              end
                      end idc
                 | _ => None
                 end.
          End invert.

          Section gallina_reify.
            Context {var : type -> Type}.
            Definition reify_list {t} (ls : list (@expr var t)) : @expr var (type.list t)
              := list_rect
                   (fun _ => _)
                   (ident.nil @@ TT)%expr
                   (fun x _ xs => ident.cons @@ (x, xs))%expr
                   ls.
          End gallina_reify.
          Section value.
            Context (var : type -> Type).
            Fixpoint value (t : type)
              := match t return Type with
                 | type.prod A B as t => value A * value B
                 | type.arrow s d => var s -> value d
                 | type.list A => list (value A)
                 | type.type_primitive _ as t
                   => type.interp t
                 end%type.
          End value.

          Section reify.
            Context {var : type -> Type}.
            Fixpoint reify {t : type} {struct t}
              : value var t -> @expr var t
              := match t return value var t -> expr t with
                 | type.prod A B as t
                   => fun '((a, b) : value var A * value var B)
                      => (@reify A a, @reify B b)%expr
                 | type.arrow s d
                   => fun (f : var s -> value var d)
                      => Abs (fun x
                              => @reify d (f x))
                 | type.list A as t
                   => fun x : list (value var A)
                      => reify_list (List.map (@reify A) x)
                 | type.type_primitive _ as t
                   => fun x : type.interp t
                      => (ident.primitive x @@ TT)%expr
                 end.
          End reify.

          Definition Reify_as (t : type) (v : forall var, value var t) : Expr t
            := fun var => reify (v _).

          Notation Reify v
            := (Reify_as (type.reify_type_of v) (fun _ => v)) (only parsing).

          Module Export Uncurry.
            Module Export type.
              Fixpoint uncurried_domain (t : type) : type
                := match t with
                   | type.arrow s d
                     => match d with
                        | type.arrow _ _
                          => s * uncurried_domain d
                        | _ => s
                        end
                   | _ => type.type_primitive type.unit
                   end%ctype.

              Definition uncurry (t : type) : type
                := type.arrow (uncurried_domain t) (type.final_codomain t).
            End type.
            Section with_var.
              Context {var : type -> Type}.

              Fixpoint uncurry' {t}
                : @expr (@expr var) t -> @expr var (type.uncurried_domain t) -> @expr var (type.final_codomain t)
                := match t return expr t -> expr (type.uncurried_domain t) -> expr (type.final_codomain t) with
                   | type.arrow s d
                     => fun e
                        => let f := fun v
                                    => @uncurry'
                                         d
                                         match invert_Abs e with
                                         | Some f => f v
                                         | None => e @ Var v
                                         end%expr in
                           match d return (expr s -> expr (type.uncurried_domain d) -> expr (type.final_codomain d)) -> expr (type.uncurried_domain (s -> d)) -> expr (type.final_codomain d) with
                           | type.arrow _ _ as d
                             => fun f sdv
                                => f (ident.fst @@ sdv) (ident.snd @@ sdv)
                           | _
                             => fun f sv => f sv TT
                           end f
                   | type.type_primitive _
                   | type.prod _ _
                   | type.list _
                     => fun e _ => unexpr e
                   end%expr.

              Definition uncurry {t} (e : @expr (@expr var) t)
                : @expr var (type.uncurry t)
                := Abs (fun v => @uncurry' t e (Var v)).
            End with_var.

            Definition Uncurry {t} (e : Expr t) : Expr (type.uncurry t)
              := fun var => uncurry (e _).

            Module CPS.
              Module Import Output.
                Module Export type.
                  Import Compilers.type.
                  Inductive type := type_primitive (_:primitive) | prod (A B : type) | continuation (A : type) | list (A : type).
                  Module Export Coercions.
                    Global Coercion type_primitive : primitive >-> type.
                  End Coercions.

                  Module Export Notations.
                    Delimit Scope cpstype_scope with cpstype.
                    Bind Scope cpstype_scope with type.
                    Notation "()" := unit : cpstype_scope.
                    Notation "A * B" := (prod A B) : cpstype_scope.
                    Notation "A --->" := (continuation A) : cpstype_scope.
                  End Notations.

                End type.

                Module expr.
                  Section expr.
                    Context {ident : type -> Type} {var : type -> Type} {R : type}.

                    Inductive expr :=
                    | Halt (v : var R)
                    | App {A} (f : var (A --->)) (x : var A)
                    | Bind {A} (x : primop A) (f : var A -> expr)
                    with
                    primop : type -> Type :=
                    | Var {t} (v : var t) : primop t
                    | Abs {t} (f : var t -> expr) : primop (t --->)
                    | Pair {A B} (x : var A) (y : var B) : primop (A * B)
                    | Fst {A B} (x : var (A * B)) : primop A
                    | Snd {A B} (x : var (A * B)) : primop B
                    | TT : primop ()
                    | Ident {t} (idc : ident t) : primop t.
                  End expr.
                  Global Arguments expr {ident var} R.
                  Global Arguments primop {ident var} R _.

                  Definition Expr {ident : type -> Type} R := forall var, @expr ident var R.

                  Module Export Notations.
                    Delimit Scope cpsexpr_scope with cpsexpr.

                    Infix "@" := App : cpsexpr_scope.
                    Notation "v <- x ; f" := (Bind x (fun v => f)) : cpsexpr_scope.
                    Notation "'λ'  x .. y , t" := (Abs (fun x => .. (Abs (fun y => t%cpsexpr)) ..)) : cpsexpr_scope.
                    Notation "( x , y , .. , z )" := (Pair .. (Pair x%cpsexpr y%cpsexpr) .. z%cpsexpr) : cpsexpr_scope.
                    Notation "()" := TT : cpsexpr_scope.
                  End Notations.
                End expr.
                Export expr.Notations.
              End Output.

              Module Export type.
                Section translate.
                  Fixpoint translate (t : Compilers.type.type) : type
                    := match t with
                       | A * B => (translate A * translate B)%cpstype
                       | s -> d => (translate s * (translate d --->) --->)%cpstype
                       | Compilers.type.list A => type.list (translate A)
                       | Compilers.type.type_primitive t
                         => t
                       end%ctype.
                  Fixpoint untranslate (R : Compilers.type.type) (t : type)
                    : Compilers.type.type
                    := match t with
                       | type.type_primitive t => t
                       | A * B => (untranslate R A * untranslate R B)%ctype
                       | (t --->)
                         => (untranslate R t -> R)%ctype
                       | type.list A => Compilers.type.list (untranslate R A)
                       end%cpstype.
                End translate.
              End type.

              Module Export expr.
                Import Output.expr.
                Import Compilers.type.
                Import Compilers.Uncurried.expr.
                Section with_ident.
                  Context {ident : Output.type.type -> Type}
                          {ident' : type -> type -> Type}
                          {var : Output.type.type -> Type}
                          (translate_ident : forall s d, ident' s d -> ident (type.translate (s -> d))).
                  Notation var' := (fun t => var (type.translate t)).
                  Local Notation oexpr := (@Output.expr.expr ident var).

                  Section splice.
                    Context {r1 r2 : Output.type.type}.
                    Fixpoint splice  (e1 : oexpr r1) (e2 : var r1 -> oexpr r2)
                             {struct e1}
                      : oexpr r2
                      := match e1 with
                         | Halt v => e2 v
                         | f @ x => f @ x
                         | Bind A x f => v <- @splice_primop _ x e2; @splice (f v) e2
                         end%cpsexpr
                    with
                    splice_primop {t} (f : @primop ident var r1 t) (e2 : var r1 -> oexpr r2)
                                  {struct f}
                    : @primop ident var r2 t
                    := match f with
                       | Output.expr.Var t v => Output.expr.Var v
                       | Output.expr.Pair A B x y as e => Output.expr.Pair x y
                       | Output.expr.Fst A B x => Output.expr.Fst x
                       | Output.expr.Snd A B x => Output.expr.Snd x
                       | Output.expr.TT => Output.expr.TT
                       | Output.expr.Ident t idc => Output.expr.Ident idc
                       | Output.expr.Abs t f
                         => Output.expr.Abs (fun x => @splice (f x) e2)
                       end.
                  End splice.

                  Local Notation "x <-- e1 ; e2" := (splice e1 (fun x => e2%cpsexpr)) : cpsexpr_scope.

                  Fixpoint translate {t}
                           (e : @Compilers.Uncurried.expr.expr ident' var' t)
                    : @Output.expr.expr ident var (type.translate t)
                    := match e with
                       | Var t v => Halt v
                       | TT => x <- () ; Halt x
                       | AppIdent s d idc args
                         => (args' <-- @translate _ args;
                               k <- Output.expr.Abs (fun r => Halt r);
                               p <- (args', k);
                               f <- Output.expr.Ident (translate_ident s d idc);
                               f @ p)
                       | Pair A B a b
                         => (a' <-- @translate _ a;
                               b' <-- @translate _ b;
                               p <- (a', b');
                               Halt p)
                       | App s d e1 e2
                         => (f <-- @translate _ e1;
                               x <-- @translate _ e2;
                               k <- Output.expr.Abs (fun r => Halt r);
                               p <- (x, k);
                               f @ p)
                       | Abs s d f
                         => f <- (Output.expr.Abs
                                    (fun p
                                     => x <- Fst p;
                                          k <- Snd p;
                                          r <-- @translate _ (f x);
                                          k @ r));
                              Halt f
                       end%cpsexpr.
                End with_ident.

                Definition Translate
                           {ident : Output.type.type -> Type}
                           {ident' : type -> type -> Type}
                           (translate_ident : forall s d, ident' s d -> ident (type.translate (s -> d)))
                           {t} (e : @Compilers.Uncurried.expr.Expr ident' t)
                  : @Output.expr.Expr ident (type.translate t)
                  := fun var => translate translate_ident (e _).

                Section call_with_cont.
                  Context {ident' : Output.type.type -> Type}
                          {ident : type -> type -> Type}
                          {var : type -> Type}
                          {r : Output.type.type}
                          {R : type}.
                  Notation ucexpr := (@Compilers.Uncurried.expr.expr ident var).
                  Notation ucexprut t := (ucexpr (type.untranslate R t)) (only parsing).
                  Notation var' := (fun t => ucexprut t).
                  Context (untranslate_ident : forall t, ident' t -> ucexprut t)
                          (ifst : forall A B, ident (A * B)%ctype A)
                          (isnd : forall A B, ident (A * B)%ctype B).

                  Fixpoint call_with_continuation
                           (e : @Output.expr.expr ident' var' r)
                           (k : ucexprut r -> ucexpr R)
                           {struct e}
                    : ucexpr R
                    := match e with
                       | Halt v => k v
                       | expr.App A f x
                         => @App _ _ (type.untranslate R A) R
                                 f x
                       | Bind A x f
                         => @call_with_continuation
                              (f (@call_primop_with_continuation A x k))
                              k
                       end%expr
                  with
                  call_primop_with_continuation
                    {t}
                    (e : @Output.expr.primop ident' var' r t)
                    (k : ucexprut r -> ucexpr R)
                    {struct e}
                  : ucexprut t
                  := match e in Output.expr.primop _ t return ucexprut t with
                     | expr.Var t v => v
                     | expr.Abs t f => Abs (fun x : var (type.untranslate _ _)
                                            => @call_with_continuation
                                                 (f (Var x)) k)
                     | expr.Pair A B x y => (x, y)
                     | Fst A B x => ifst (type.untranslate _ A) (type.untranslate _ B)
                                         @@ x
                     | Snd A B x => isnd (type.untranslate _ A) (type.untranslate _ B)
                                         @@ x
                     | expr.TT => TT
                     | Ident t idc => untranslate_ident t idc
                     end%expr.
                End call_with_cont.
              End expr.

              Module Export ident.

                Inductive ident : type -> Set :=
                | wrap {s d} (idc : Uncurried.expr.default.ident s d) : ident (type.translate (s -> d)).

                Local Notation var_eta x := (ident.fst @@ x, ident.snd @@ x)%core%expr.

                Definition untranslate {R} {t} (idc : ident t)
                  : @Compilers.Uncurried.expr.Expr Uncurried.expr.default.ident (type.untranslate R t)
                  := fun var
                     => match idc in ident t return @Compilers.Uncurried.expr.expr Uncurried.expr.default.ident var (type.untranslate R t) with
                        | wrap s d idc
                          =>
                          match idc in default.ident s d return @Compilers.Uncurried.expr.expr Uncurried.expr.default.ident var (type.untranslate R (type.translate (s -> d))) with
                          | ident.primitive t v
                            => λ (_k :
                                    var (() * (t -> R))%ctype) ,
                               (ident.snd @@ (Var _k))
                                 @ (ident.primitive v @@ TT)
                          | ident.Let_In tx tC
                            => λ (xyk :
                                    var (type.untranslate _ (type.translate tx) * (type.untranslate _ (type.translate tx) * (type.untranslate _ (type.translate tC) -> R) -> R) * (type.untranslate _ (type.translate tC) -> R))%ctype) ,
                               ident.Let_In
                                 @@ (ident.fst @@ (ident.fst @@ (Var xyk)),
                                     (λ (x :
                                           var (type.untranslate _ (type.translate tx))) ,
                                      (ident.snd @@ (ident.fst @@ (Var xyk)))
                                        @ (Var x, ident.snd @@ Var xyk)))
                          | ident.nat_rect P
                            => λ (PO_PS_n_k :
                                    var ((Compilers.type.type_primitive ()%cpstype * (type.untranslate R (type.translate P) -> R) -> R) * (Compilers.type.type_primitive type.nat * type.untranslate R (type.translate P) * (type.untranslate R (type.translate P) -> R) -> R) * Compilers.type.type_primitive type.nat * (type.untranslate R (type.translate P) -> R))%ctype) ,
                               let (PO_PS_n, k) := var_eta (Var PO_PS_n_k) in
                               let (PO_PS, n) := var_eta PO_PS_n in
                               let (PO, PS) := var_eta PO_PS in
                               ((@ident.nat_rect ((type.untranslate _ (type.translate P) -> R) -> R))
                                  @@ ((λ tt k , PO @ (Var tt, Var k)),
                                      (λ n'rec k ,
                                       let (n', rec) := var_eta (Var n'rec) in
                                       rec @ (λ rec , PS @ (n', Var rec, Var k))),
                                      n))
                                 @ k
                          | ident.list_rect A P
                            => λ (Pnil_Pcons_ls_k :
                                    var ((Compilers.type.type_primitive ()%cpstype * (type.untranslate R (type.translate P) -> R) -> R) * (type.untranslate R (type.translate A) * Compilers.type.list (type.untranslate R (type.translate A)) * type.untranslate R (type.translate P) * (type.untranslate R (type.translate P) -> R) -> R) * Compilers.type.list (type.untranslate R (type.translate A)) * (type.untranslate R (type.translate P) -> R))%ctype) ,
                               let (Pnil_Pcons_ls, k) := var_eta (Var Pnil_Pcons_ls_k) in
                               let (Pnil_Pcons, ls) := var_eta Pnil_Pcons_ls in
                               let (Pnil, Pcons) := var_eta Pnil_Pcons in
                               ((@ident.list_rect
                                   (type.untranslate _ (type.translate A))
                                   ((type.untranslate _ (type.translate P) -> R) -> R))
                                  @@ ((λ tt k, Pnil @ (Var tt, Var k)),
                                      (λ x_xs_rec k,
                                       let (x_xs, rec) := var_eta (Var x_xs_rec) in
                                       let (x, xs) := var_eta x_xs in
                                       rec @ (λ rec , Pcons @ (x, xs, Var rec, Var k))),
                                      ls))
                                 @ k
                          | ident.List_nth_default T
                            => λ (xyzk :
                                    var (type.untranslate _ (type.translate T) * Compilers.type.list (type.untranslate _ (type.translate T)) * type.nat * (type.untranslate _ (type.translate T) -> R))%ctype) ,
                               (ident.snd @@ Var xyzk)
                                 @ (ident.List_nth_default @@ (ident.fst @@ Var xyzk))
                          | ident.List_nth_default_concrete T d n
                            => λ (xk :
                                    var (Compilers.type.list (type.untranslate R (type.translate T)) * (type.untranslate R (type.translate T) -> R))%ctype) ,
                               (ident.snd @@ Var xk)
                                 @ (ident.List_nth_default_concrete d n @@ (ident.fst @@ Var xk))
                          | ident.bool_rect T
                            => λ (xyzk :
                                    var ((Compilers.type.type_primitive ()%cpstype * (type.untranslate R (type.translate T) -> R) -> R) * (Compilers.type.type_primitive ()%cpstype * (type.untranslate R (type.translate T) -> R) -> R) * Compilers.type.type_primitive type.bool * (type.untranslate R (type.translate T) -> R))%ctype) ,
                               ident.bool_rect
                                 @@ ((λ tt,
                                      (ident.fst @@ (ident.fst @@ (ident.fst @@ (Var xyzk))))
                                        @ (Var tt, (ident.snd @@ (Var xyzk)))),
                                     (λ tt,
                                      (ident.snd @@ (ident.fst @@ (ident.fst @@ (Var xyzk))))
                                        @ (Var tt, (ident.snd @@ (Var xyzk)))),
                                     ident.snd @@ (ident.fst @@ (Var xyzk)))
                          | ident.nil t
                            => λ (_k :
                                    var (() * (Compilers.type.list (type.untranslate _ (type.translate t)) -> R))%ctype) ,
                               (ident.snd @@ (Var _k))
                                 @ (ident.nil @@ TT)
                          | ident.cons t
                            => λ (xyk :
                                    var (type.untranslate _ (type.translate t) * Compilers.type.list (type.untranslate _ (type.translate t)) * (Compilers.type.list (type.untranslate _ (type.translate t)) -> R))%ctype) ,
                               (ident.snd @@ (Var xyk))
                                 @ (ident.cons
                                      @@ (ident.fst @@ (Var xyk)))
                          | ident.fst A B
                            => λ (xk :
                                    var (type.untranslate _ (type.translate A) * type.untranslate _ (type.translate B) * (type.untranslate _ (type.translate A) -> R))%ctype) ,
                               (ident.snd @@ (Var xk))
                                 @ (ident.fst
                                      @@ (ident.fst @@ (Var xk)))
                          | ident.snd A B
                            => λ (xk :
                                    var (type.untranslate _ (type.translate A) * type.untranslate _ (type.translate B) * (type.untranslate _ (type.translate B) -> R))%ctype) ,
                               (ident.snd @@ (Var xk))
                                 @ (ident.snd
                                      @@ (ident.fst @@ (Var xk)))
                          | ident.Nat_succ as idc
                          | ident.pred as idc
                            => λ (xyk :
                                    var (type.nat * (type.nat -> R))%ctype) ,
                               (ident.snd @@ (Var xyk))
                                 @ ((idc : default.ident _ type.nat)
                                      @@ (ident.fst @@ (Var xyk)))
                          | ident.Nat_add as idc
                          | ident.Nat_sub as idc
                          | ident.Nat_mul as idc
                          | ident.Nat_max as idc
                            => λ (xyk :
                                    var (type.nat * type.nat * (type.nat -> R))%ctype) ,
                               (ident.snd @@ (Var xyk))
                                 @ ((idc : default.ident _ type.nat)
                                      @@ (ident.fst @@ (Var xyk)))
                          | ident.Z_shiftr _ as idc
                          | ident.Z_shiftl _ as idc
                          | ident.Z_land _ as idc
                          | ident.Z_opp as idc
                          | ident.Z_cast _ as idc
                            => λ (xyk :
                                    var (type.Z * (type.Z -> R))%ctype) ,
                               (ident.snd @@ (Var xyk))
                                 @ ((idc : default.ident _ type.Z)
                                      @@ (ident.fst @@ (Var xyk)))
                          | ident.Z_add as idc
                          | ident.Z_mul as idc
                          | ident.Z_sub as idc
                          | ident.Z_pow as idc
                          | ident.Z_div as idc
                          | ident.Z_modulo as idc
                            => λ (xyk :
                                    var (type.Z * type.Z * (type.Z -> R))%ctype) ,
                               (ident.snd @@ (Var xyk))
                                 @ ((idc : default.ident _ type.Z)
                                      @@ (ident.fst @@ (Var xyk)))
                          | ident.Z_eqb as idc
                          | ident.Z_leb as idc
                            => λ (xyk :
                                    var (type.Z * type.Z * (type.bool -> R))%ctype) ,
                               (ident.snd @@ (Var xyk))
                                 @ ((idc : default.ident _ type.bool)
                                      @@ (ident.fst @@ (Var xyk)))
                          | ident.Z_of_nat as idc
                            => λ (xyk :
                                    var (type.nat * (type.Z -> R))%ctype) ,
                               (ident.snd @@ (Var xyk))
                                 @ ((idc : default.ident _ type.Z)
                                      @@ (ident.fst @@ (Var xyk)))
                          | ident.Z_cast2 _ as idc
                            => λ (xyk :
                                    var (type.Z * type.Z * ((type.Z * type.Z) -> R))%ctype) ,
                               (ident.snd @@ (Var xyk))
                                 @ ((idc : default.ident _ (type.Z * type.Z))
                                      @@ (ident.fst @@ (Var xyk)))
                          end%expr
                        end.
              End ident.

              Module Export default.
                Notation expr := (@Output.expr.expr ident).
                Notation Expr := (@Output.expr.Expr ident).

                Definition Translate
                           {t} (e : @Compilers.Uncurried.expr.default.Expr t)
                  : Expr (type.translate t)
                  := expr.Translate (@ident.wrap) e.

                Definition call_with_continuation
                           {var}
                           {R : Compilers.type.type}
                           {t} (e : @expr _ t)
                           (k : @Uncurried.expr.default.expr var (type.untranslate R t) -> @Uncurried.expr.default.expr var R)
                  : @Compilers.Uncurried.expr.default.expr var R
                  := expr.call_with_continuation (fun t idc => @ident.untranslate _ t idc _) (@ident.fst) (@ident.snd) e k.

                Local Notation iffT A B := ((A -> B) * (B -> A))%type.

                Fixpoint try_untranslate_translate {R} {t}
                  : option (forall (P : Compilers.type.type -> Type),
                               iffT (P (type.untranslate R (type.translate t))) (P t))
                  := match t return option (forall (P : Compilers.type.type -> Type),
                                               iffT (P (type.untranslate R (type.translate t))) (P t)) with
                     | Compilers.type.type_primitive x
                       => Some (fun P => ((fun v => v), (fun v => v)))
                     | type.arrow s d => None
                     | Compilers.type.prod A B
                       => (fA <- (@try_untranslate_translate _ A);
                             fB <- (@try_untranslate_translate _ B);
                             Some
                               (fun P
                                => let fA := fA (fun A => P (Compilers.type.prod A (type.untranslate R (type.translate B)))) in
                                   let fB := fB (fun B => P (Compilers.type.prod A B)) in
                                   ((fun v => fst fB (fst fA v)),
                                    (fun v => snd fA (snd fB v)))))%option
                     | Compilers.type.list A
                       => (fA <- (@try_untranslate_translate R A);
                             Some (fun P => fA (fun A => P (Compilers.type.list A))))%option
                     end.

                Local Notation "x <-- e1 ; e2" := (expr.splice e1 (fun x => e2%cpsexpr)) : cpsexpr_scope.

                Definition call_fun_with_id_continuation'
                           {s d}
                  : option (forall var
                                   (e : @expr _ (type.translate (s -> d))),
                               @Compilers.Uncurried.expr.default.expr var (s -> d))
                  := (fs <- (@try_untranslate_translate _ s);
                        fd <- (@try_untranslate_translate _ d);
                        Some
                          (fun var e
                           => let P := @Compilers.Uncurried.expr.default.expr var in
                              Abs
                                (fun v : var s
                                 => call_with_continuation
                                      ((f <-- e;
                                          k <- (λ r, expr.Halt r);
                                          p <- (snd (fs P) (Var v), k);
                                          f @ p)%cpsexpr)
                                      (fst (fd P)))))%option.

                Definition CallFunWithIdContinuation
                           {s d}
                           (e : Expr (type.translate (s -> d)))
                  : option (@Compilers.Uncurried.expr.default.Expr (s -> d))
                  := option_map
                       (fun f var => f _ (e _))
                       (@call_fun_with_id_continuation' s d).
              End default.
              Include default.
            End CPS.

            Module ZRange.
              Module type.
                Module Export primitive.

                  Definition interp (t : type.primitive) : Set
                    := match t with
                       | type.unit => unit
                       | type.Z => zrange
                       | type.nat => unit
                       | type.bool => unit
                       end.
                  Module Export option.

                    Definition interp (t : type.primitive) : Set
                      := match t with
                         | type.unit => unit
                         | type.Z => option zrange
                         | type.nat => unit
                         | type.bool => unit
                         end.
                    Definition None {t} : interp t
                      := match t with
                         | type.Z => None
                         | _ => tt
                         end.
                    Definition Some {t} : primitive.interp t -> interp t
                      := match t with
                         | type.Z => Some
                         | _ => id
                         end.
                  End option.
                End primitive.

                Fixpoint interp (t : type) : Set
                  := match t with
                     | type.type_primitive x => primitive.interp x
                     | type.prod A B => interp A * interp B
                     | type.arrow s d => interp s -> interp d
                     | type.list A => list (interp A)
                     end.
                Module Export option.

                  Fixpoint interp (t : type) : Set
                    := match t with
                       | type.type_primitive x => primitive.option.interp x
                       | type.prod A B => interp A * interp B
                       | type.arrow s d => interp s -> interp d
                       | type.list A => option (list (interp A))
                       end.
                  Fixpoint None {t : type} : interp t
                    := match t with
                       | type.type_primitive x => @primitive.option.None x
                       | type.prod A B => (@None A, @None B)
                       | type.arrow s d => fun _ => @None d
                       | type.list A => Datatypes.None
                       end.
                  Fixpoint Some {t : type} : type.interp t -> interp t
                    := match t with
                       | type.type_primitive x => @primitive.option.Some x
                       | type.prod A B
                         => fun x : type.interp A * type.interp B
                            => (@Some A (fst x), @Some B (snd x))
                       | type.arrow s d => fun _ _ => @None d
                       | type.list A => fun ls => Datatypes.Some (List.map (@Some A) ls)
                       end.
                End option.
              End type.

              Module Export ident.
                Module Export option.

                  Notation curry0 f
                    := (fun 'tt => f).
                  Notation curry2 f
                    := (fun '(a, b) => f a b).
                  Notation uncurry2 f
                    := (fun a b => f (a, b)).

                  Definition interp {s d} (idc : ident s d) : type.option.interp s -> type.option.interp d
                    := match idc in ident.ident s d return type.option.interp s -> type.option.interp d with
                       | ident.primitive type.Z v => fun _ => Some r[v ~> v]
                       | ident.Let_In tx tC => fun '(x, C) => C x
                       | ident.primitive _ _
                       | ident.Nat_succ
                       | ident.Nat_add
                       | ident.Nat_sub
                       | ident.Nat_mul
                       | ident.Nat_max
                       | ident.bool_rect _
                       | ident.nat_rect _
                       | ident.pred
                       | ident.list_rect _ _
                       | ident.List_nth_default _
                       | ident.Z_pow
                       | ident.Z_div
                       | ident.Z_eqb
                       | ident.Z_leb
                       | ident.Z_of_nat
                       | ident.Z_modulo
                         => fun _ => type.option.None
                       | ident.nil t => curry0 (Some (@nil (type.option.interp t)))
                       | ident.cons t => curry2 (fun a => option_map (@Datatypes.cons (type.option.interp t) a))
                       | ident.fst A B => @Datatypes.fst (type.option.interp A) (type.option.interp B)
                       | ident.snd A B => @Datatypes.snd (type.option.interp A) (type.option.interp B)
                       | ident.List_nth_default_concrete T d n
                         => fun ls
                            => match ls with
                               | Datatypes.Some ls
                                 => @nth_default (type.option.interp T) type.option.None ls n
                               | Datatypes.None
                                 => type.option.None
                               end
                       | ident.Z_shiftr _ as idc
                       | ident.Z_shiftl _ as idc
                       | ident.Z_opp as idc
                         => option_map (ZRange.two_corners (ident.interp idc))
                       | ident.Z_land mask
                         => option_map
                              (fun r : zrange
                               => ZRange.land_bounds r r[mask~>mask])
                       | ident.Z_add as idc
                       | ident.Z_mul as idc
                       | ident.Z_sub as idc
                         => fun '((x, y) : option zrange * option zrange)
                            => match x, y with
                               | Some x, Some y
                                 => Some (ZRange.four_corners (uncurry2 (ident.interp idc)) x y)
                               | Some _, None | None, Some _ | None, None => None
                               end
                       | ident.Z_cast range
                         => fun r : option zrange
                            => Some match r with
                                    | Some r => ZRange.intersection r range
                                    | None => range
                                    end
                       | ident.Z_cast2 (r1, r2)
                         => fun '((r1', r2') : option zrange * option zrange)
                            => (Some match r1' with
                                     | Some r => ZRange.intersection r r1
                                     | None => r1
                                     end,
                                Some match r2' with
                                     | Some r => ZRange.intersection r r2
                                     | None => r2
                                     end)
                       end.
                End option.
              End ident.
            End ZRange.

            Module Export DefaultValue.

              Module Export type.
                Module Export primitive.
                  Definition default {t : type.primitive} : type.interp t
                    := match t with
                       | type.unit => tt
                       | type.Z => (-1)%Z
                       | type.nat => 0%nat
                       | type.bool => true
                       end.
                End primitive.
              End type.

              Module Export expr.
                Section with_var.
                  Context {var : type -> Type}.
                  Fixpoint default {t : type} : @expr var t
                    := match t with
                       | type.type_primitive x
                         => AppIdent (ident.primitive type.primitive.default) TT
                       | type.prod A B
                         => (@default A, @default B)
                       | type.arrow s d => Abs (fun _ => @default d)
                       | type.list A => AppIdent ident.nil TT
                       end.
                End with_var.

                Module Flat.
                  Inductive expr : type -> Set :=
                  | Var (t : type) (n : positive) : expr t
                  | TT : expr type.unit
                  | AppIdent {s d} (idc : ident s d) (arg : expr s) : expr d
                  | App {s d} (f : expr (s -> d)) (x : expr s) : expr d
                  | Pair {A B} (a : expr A) (b : expr B) : expr (A * B)
                  | Abs (s : type) (n : positive) {d} (f : expr d) : expr (s -> d).
                End Flat.

                Definition ERROR {T} (v : T) : T.
                  exact v.
                Qed.

                Fixpoint to_flat' {t} (e : @expr (fun _ => PositiveMap.key) t)
                         (cur_idx : PositiveMap.key)
                  : Flat.expr t
                  := match e in expr.expr t return Flat.expr t with
                     | Var t v => Flat.Var t v
                     | TT => Flat.TT
                     | AppIdent s d idc args
                       => Flat.AppIdent idc (@to_flat' _ args cur_idx)
                     | App s d f x => Flat.App
                                        (@to_flat' _ f cur_idx)
                                        (@to_flat' _ x cur_idx)
                     | Pair A B a b => Flat.Pair
                                         (@to_flat' _ a cur_idx)
                                         (@to_flat' _ b cur_idx)
                     | Abs s d f
                       => Flat.Abs s cur_idx
                                   (@to_flat'
                                      d (f cur_idx)
                                      (Pos.succ cur_idx))
                     end.

                Fixpoint from_flat {t} (e : Flat.expr t)
                  : forall var, PositiveMap.t { t : type & unit -> var t } -> @expr var t
                  := match e in Flat.expr t return forall var, PositiveMap.t { t : type & unit -> var t } -> expr t with
                     | Flat.Var t v
                       => fun var ctx
                          => match (tv <- PositiveMap.find v ctx;
                                      type.try_transport var _ _ (projT2 tv tt))%option with
                             | Some v => Var v
                             | None => ERROR DefaultValue.expr.default
                             end
                     | Flat.TT => fun _ _ => TT
                     | Flat.AppIdent s d idc args
                       => let args' := @from_flat _ args in
                          fun var ctx => AppIdent idc (args' var ctx)
                     | Flat.App s d f x
                       => let f' := @from_flat _ f in
                          let x' := @from_flat _ x in
                          fun var ctx => App (f' var ctx) (x' var ctx)
                     | Flat.Pair A B a b
                       => let a' := @from_flat _ a in
                          let b' := @from_flat _ b in
                          fun var ctx => Pair (a' var ctx) (b' var ctx)
                     | Flat.Abs s cur_idx d f
                       => let f' := @from_flat d f in
                          fun var ctx
                          => Abs (fun v => f' var (PositiveMap.add cur_idx (existT _ s (fun _ => v)) ctx))
                     end.

                Definition to_flat {t} (e : expr t) : Flat.expr t
                  := to_flat' e 1%positive.
                Definition ToFlat {t} (E : Expr t) : Flat.expr t
                  := to_flat (E _).
                Definition FromFlat {t} (e : Flat.expr t) : Expr t
                  := let e' := @from_flat t e in
                     fun var => e' var (PositiveMap.empty _).

                Module Export partial.
                  Notation data := ZRange.type.option.interp.
                  Section value.
                    Context (var : type -> Type).
                    Definition value_prestep (value : type -> Type) (t : type)
                      := match t return Type with
                         | type.prod A B as t => value A * value B
                         | type.arrow s d => value s -> value d
                         | type.list A => list (value A)
                         | type.type_primitive _ as t
                           => type.interp t
                         end%type.
                    Definition value_step (value : type -> Type) (t : type)
                      := match t return Type with
                         | type.arrow _ _ as t
                           => value_prestep value t
                         | type.prod _ _ as t
                         | type.list _ as t
                         | type.type_primitive _ as t
                           => data t * @expr var t + value_prestep value t
                         end%type.
                    Fixpoint value (t : type)
                      := value_step value t.

                    Fixpoint data_from_value {t} : value t -> data t
                      := match t return value t -> data t with
                         | type.arrow _ _ as t
                           => fun _ => ZRange.type.option.None
                         | type.prod A B as t
                           => fun v
                              => match v with
                                 | inl (data, _) => data
                                 | inr (a, b)
                                   => (@data_from_value A a, @data_from_value B b)
                                 end
                         | type.list A as t
                           => fun v
                              => match v with
                                 | inl (data, _) => data
                                 | inr ls
                                   => Some (List.map (@data_from_value A) ls)
                                 end
                         | type.type_primitive type.Z as t
                           => fun v
                              => match v with
                                 | inl (data, _) => data
                                 | inr v => Some r[v~>v]%zrange
                                 end
                         | type.type_primitive _ as t
                           => fun v
                              => match v with
                                 | inl (data, _) => data
                                 | inr _ => ZRange.type.option.None
                                 end
                         end.
                  End value.

                  Module Export expr.
                    Section reify.
                      Context {var : type -> Type}.
                      Fixpoint reify {t : type} {struct t}
                        : value var t -> @expr var t
                        := match t return value var t -> expr t with
                           | type.prod A B as t
                             => fun x : (data A * data B) * expr t + value var A * value var B
                                => match x with
                                   | inl ((da, db), v)
                                     => match A, B return data A -> data B -> expr (A * B) -> expr (A * B) with
                                        | type.Z, type.Z
                                          => fun da db v
                                             => match da, db with
                                                | Some r1, Some r2
                                                  => (ident.Z.cast2 (r1, r2)%core @@ v)%expr
                                                | _, _ => v
                                                end
                                        | _, _ => fun _ _ v => v
                                        end da db v
                                   | inr (a, b) => (@reify A a, @reify B b)%expr
                                   end
                           | type.arrow s d
                             => fun (f : value var s -> value var d)
                                => Abs (fun x
                                        => @reify d (f (@reflect s (Var x))))
                           | type.list A as t
                             => fun x : _ * expr t + list (value var A)
                                => match x with
                                   | inl (_, v) => v
                                   | inr v => reify_list (List.map (@reify A) v)
                                   end
                           | type.type_primitive type.Z as t
                             => fun x : _ * expr t + type.interp t
                                => match x with
                                   | inl (Some r, v) => ident.Z.cast r @@ v
                                   | inl (None, v) => v
                                   | inr v => ident.primitive v @@ TT
                                   end%core%expr
                           | type.type_primitive _ as t
                             => fun x : _ * expr t + type.interp t
                                => match x with
                                   | inl (_, v) => v
                                   | inr v => ident.primitive v @@ TT
                                   end%core%expr
                           end
                      with reflect {t : type}
                           : @expr var t -> value var t
                           := match t return expr t -> value var t with
                              | type.arrow s d
                                => fun (f : expr (s -> d)) (x : value var s)
                                   => @reflect d (App f (@reify s x))
                              | type.prod A B as t
                                => fun v : expr t
                                   => let inr := @inr (data t * expr t) (value_prestep (value var) t) in
                                      let inl := @inl (data t * expr t) (value_prestep (value var) t) in
                                      match invert_Pair v with
                                      | Some (a, b)
                                        => inr (@reflect A a, @reflect B b)
                                      | None
                                        => inl
                                             (match A, B return expr (A * B) -> data (A * B) * expr (A * B) with
                                              | type.Z, type.Z
                                                => fun v
                                                   => match invert_Z_cast2 v with
                                                      | Some (r, v)
                                                        => (ZRange.type.option.Some (t:=type.Z*type.Z) r, v)
                                                      | None
                                                        => (ZRange.type.option.None, v)
                                                      end
                                              | _, _ => fun v => (ZRange.type.option.None, v)
                                              end v)
                                      end
                              | type.list A as t
                                => fun v : expr t
                                   => let inr := @inr (data t * expr t) (value_prestep (value var) t) in
                                      let inl := @inl (data t * expr t) (value_prestep (value var) t) in
                                      match reflect_list v with
                                      | Some ls
                                        => inr (List.map (@reflect A) ls)
                                      | None
                                        => inl (None, v)
                                      end
                              | type.type_primitive type.Z as t
                                => fun v : expr t
                                   => let inr' := @inr (data t * expr t) (value_prestep (value var) t) in
                                      let inl' := @inl (data t * expr t) (value_prestep (value var) t) in
                                      match reflect_primitive v, invert_Z_cast v with
                                      | Some v, _ => inr' v
                                      | None, Some (r, v) => inl' (Some r, v)
                                      | None, None => inl' (None, v)
                                      end
                              | type.type_primitive _ as t
                                => fun v : expr t
                                   => let inr := @inr (data t * expr t) (value_prestep (value var) t) in
                                      let inl := @inl (data t * expr t) (value_prestep (value var) t) in
                                      match reflect_primitive v with
                                      | Some v => inr v
                                      | None => inl (tt, v)
                                      end
                              end.
                    End reify.
                  End expr.

                  Module Export ident.
                    Section interp.
                      Context (inline_var_nodes : bool)
                              {var : type -> Type}.
                      Fixpoint is_var_like {t} (e : @expr var t) : bool
                        := match e with
                           | Var t v => true
                           | TT => true
                           | AppIdent _ _ (ident.fst _ _) args => @is_var_like _ args
                           | AppIdent _ _ (ident.snd _ _) args => @is_var_like _ args
                           | AppIdent _ _ (ident.Z.cast _) args => @is_var_like _ args
                           | AppIdent _ _ (ident.Z.cast2 _) args => @is_var_like _ args
                           | Pair A B a b => @is_var_like A a && @is_var_like B b
                           | AppIdent _ _ _ _ => false
                           | App _ _ _ _
                           | Abs _ _ _
                             => false
                           end.

                      Fixpoint interp_let_in {tC tx : type} {struct tx} : value var tx -> (value var tx -> value var tC) -> value var tC
                        := match tx return value var tx -> (value var tx -> value var tC) -> value var tC with
                           | type.arrow _ _
                             => fun x f => f x
                           | type.list T as t
                             => fun (x : data t * expr t + list (value var T)) (f : data t * expr t + list (value var T) -> value var tC)
                                => match x with
                                   | inr ls
                                     => list_rect
                                          (fun _ => (list (value var T) -> value var tC) -> value var tC)
                                          (fun f => f nil)
                                          (fun x _ rec f
                                           => rec (fun ls => @interp_let_in
                                                               _ T x
                                                               (fun x => f (cons x ls))))
                                          ls
                                          (fun ls => f (inr ls))
                                   | inl e => f (inl e)
                                   end
                           | type.prod A B as t
                             => fun (x : data t * expr t + value var A * value var B) (f : data t * expr t + value var A * value var B -> value var tC)
                                => match x with
                                   | inr (a, b)
                                     => @interp_let_in
                                          _ A a
                                          (fun a
                                           => @interp_let_in
                                                _ B b
                                                (fun b => f (inr (a, b))))
                                   | inl (data, e)
                                     => if inline_var_nodes && is_var_like e
                                        then f x
                                        else partial.expr.reflect
                                               (expr_let y := partial.expr.reify (t:=t) x in
                                                    partial.expr.reify (f (inl (data, Var y)%core)))%expr
                                   end
                           | type.type_primitive _ as t
                             => fun (x : data t * expr t + type.interp t) (f : data t * expr t + type.interp t -> value var tC)
                                => match x with
                                   | inl (data, e)
                                     => if inline_var_nodes && is_var_like e
                                        then f x
                                        else partial.expr.reflect
                                               (expr_let y := (partial.expr.reify (t:=t) x) in
                                                    partial.expr.reify (f (inl (data, Var y)%core)))%expr
                                   | inr v => f (inr v)
                                   end
                           end.

                      Let default_interp
                          {s d}
                        : ident s d -> value var s -> value var d
                        := match d return ident s d -> value var s -> value var d with
                           | type.arrow _ _
                             => fun idc args => expr.reflect (AppIdent idc (expr.reify args))
                           | _
                             => fun idc args
                                => inl (ZRange.ident.option.interp idc (data_from_value var args),
                                        AppIdent idc (expr.reify args))
                           end.

                      Definition interp {s d} (idc : ident s d) : value var (s -> d)
                        := match idc in ident s d return value var (s -> d) with
                           | ident.Let_In tx tC as idc
                             => fun (xf : data (tx * (tx -> tC)) * expr (tx * (tx -> tC)) + value var tx * value var (tx -> tC))
                                => match xf with
                                   | inr (x, f) => interp_let_in x f
                                   | _ => expr.reflect (AppIdent idc (expr.reify (t:=tx * (tx -> tC)) xf))
                                   end
                           | ident.nil t
                             => fun _ => inr (@nil (value var t))
                           | ident.primitive t v
                             => fun _ => inr v
                           | ident.cons t as idc
                             => fun (x_xs : data (t * type.list t) * expr (t * type.list t) + value var t * (data (type.list t) * expr (type.list t) + list (value var t)))
                                => match x_xs return data (type.list t) * expr (type.list t) + list (value var t) with
                                   | inr (x, inr xs) => inr (cons x xs)
                                   | _
                                     => default_interp idc x_xs
                                   end
                           | ident.fst A B as idc
                             => fun x : data (A * B) * expr (A * B) + value var A * value var B
                                => match x with
                                   | inr x => fst x
                                   | _ => default_interp idc x
                                   end
                           | ident.snd A B as idc
                             => fun x : data (A * B) * expr (A * B) + value var A * value var B
                                => match x with
                                   | inr x => snd x
                                   | _ => default_interp idc x
                                   end
                           | ident.bool_rect T as idc
                             => fun (true_case_false_case_b : data ((type.unit -> T) * (type.unit -> T) * type.bool) * expr ((type.unit -> T) * (type.unit -> T) * type.bool) + (data ((type.unit -> T) * (type.unit -> T)) * expr ((type.unit -> T) * (type.unit -> T)) + (_ + Datatypes.unit -> value var T) * (_ + Datatypes.unit -> value var T)) * (data type.bool * expr type.bool + bool))
                                => match true_case_false_case_b with
                                   | inr (inr (true_case, false_case), inr b)
                                     => if b then true_case (inr tt) else false_case (inr tt)
                                   | _ => default_interp idc true_case_false_case_b
                                   end
                           | ident.nat_rect P as idc
                             => fun (O_case_S_case_n : _ * expr ((type.unit -> P) * (type.nat * P -> P) * type.nat) + (_ * expr ((type.unit -> P) * (type.nat * P -> P)) + (_ + Datatypes.unit -> value var P) * value var (type.nat * P -> P)) * (_ * expr type.nat + nat))
                                => match O_case_S_case_n with
                                   | inr (inr (O_case, S_case), inr n)
                                     => @nat_rect (fun _ => value var P)
                                                  (O_case (inr tt))
                                                  (fun n' rec => S_case (inr (inr n', rec)))
                                                  n
                                   | _ => default_interp idc O_case_S_case_n
                                   end
                           | ident.list_rect A P as idc
                             => fun (nil_case_cons_case_ls : _ * expr ((type.unit -> P) * (A * type.list A * P -> P) * type.list A) + (_ * expr ((type.unit -> P) * (A * type.list A * P -> P)) + (_ + Datatypes.unit -> value var P) * value var (A * type.list A * P -> P)) * (_ * expr (type.list A) + list (value var A)))
                                => match nil_case_cons_case_ls with
                                   | inr (inr (nil_case, cons_case), inr ls)
                                     => @list_rect
                                          (value var A)
                                          (fun _ => value var P)
                                          (nil_case (inr tt))
                                          (fun x xs rec => cons_case (inr (inr (x, inr xs), rec)))
                                          ls
                                   | _ => default_interp idc nil_case_cons_case_ls
                                   end
                           | ident.List.nth_default type.Z as idc
                             => fun (default_ls_idx : _ * expr (type.Z * type.list type.Z * type.nat) + (_ * expr (type.Z * type.list type.Z) + (_ * expr type.Z + type.interp type.Z) * (_ * expr (type.list type.Z) + list (value var type.Z))) * (_ * expr type.nat + nat))
                                => match default_ls_idx with
                                   | inr (inr (default, inr ls), inr idx)
                                     => List.nth_default default ls idx
                                   | inr (inr (inr default, ls), inr idx)
                                     => default_interp (ident.List.nth_default_concrete default idx) ls
                                   | _ => default_interp idc default_ls_idx
                                   end
                           | ident.List.nth_default (type.type_primitive A) as idc
                             => fun (default_ls_idx : _ * expr (A * type.list A * type.nat) + (_ * expr (A * type.list A) + (_ * expr A + type.interp A) * (_ * expr (type.list A) + list (value var A))) * (_ * expr type.nat + nat))
                                => match default_ls_idx with
                                   | inr (inr (default, inr ls), inr idx)
                                     => List.nth_default default ls idx
                                   | inr (inr (inr default, ls), inr idx)
                                     => default_interp (ident.List.nth_default_concrete default idx) ls
                                   | _ => default_interp idc default_ls_idx
                                   end
                           | ident.List.nth_default A as idc
                             => fun (default_ls_idx : _ * expr (A * type.list A * type.nat) + (_ * expr (A * type.list A) + value var A * (_ * expr (type.list A) + list (value var A))) * (_ * expr type.nat + nat))
                                => match default_ls_idx with
                                   | inr (inr (default, inr ls), inr idx)
                                     => List.nth_default default ls idx
                                   | _ => default_interp idc default_ls_idx
                                   end
                           | ident.List.nth_default_concrete A default idx as idc
                             => fun (ls : _ * expr (type.list A) + list (value var A))
                                => match ls with
                                   | inr ls
                                     => List.nth_default (expr.reflect (t:=A) (AppIdent (ident.primitive default) TT)) ls idx
                                   | _ => default_interp idc ls
                                   end
                           | ident.pred as idc
                           | ident.Nat_succ as idc
                             => fun x : _ * expr _ + type.interp _
                                => match x return _ * expr _ + type.interp _ with
                                   | inr x => inr (ident.interp idc x)
                                   | _ => default_interp idc x
                                   end
                           | ident.Z_of_nat as idc
                             => fun x : _ * expr _ + type.interp _
                                => match x return _ * expr _ + type.interp _ with
                                   | inr x => inr (ident.interp idc x)
                                   | _ => default_interp idc x
                                   end
                           | ident.Z_opp as idc
                             => fun x : _ * expr _ + type.interp _
                                => match x return _ * expr _ + type.interp _ with
                                   | inr x => inr (ident.interp idc x)
                                   | inl (r, x)
                                     => match invert_Z_opp x with
                                        | Some x => inl (r, x)
                                        | None => inl (ZRange.ident.option.interp idc r, AppIdent idc x)
                                        end
                                   end
                           | ident.Z_shiftr _ as idc
                           | ident.Z_shiftl _ as idc
                           | ident.Z_land _ as idc
                             => fun x : _ * expr _ + type.interp _
                                => match x return _ * expr _ + type.interp _ with
                                   | inr x => inr (ident.interp idc x)
                                   | inl (data, e)
                                     => inl (ZRange.ident.option.interp idc data,
                                             AppIdent idc (expr.reify (t:=type.Z) x))
                                   end
                           | ident.Nat_add as idc
                           | ident.Nat_sub as idc
                           | ident.Nat_mul as idc
                           | ident.Nat_max as idc
                           | ident.Z_eqb as idc
                           | ident.Z_leb as idc
                           | ident.Z_pow as idc
                             => fun (x_y : data (_ * _) * expr (_ * _) + (_ + type.interp _) * (_ + type.interp _))
                                => match x_y return _ + type.interp _ with
                                   | inr (inr x, inr y) => inr (ident.interp idc (x, y))
                                   | _ => default_interp idc x_y
                                   end
                           | ident.Z_div as idc
                             => fun (x_y : _ * expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _))
                                => let default _ := default_interp idc x_y in
                                   match x_y return _ * expr _ + type.interp _ with
                                   | inr (inr x, inr y) => inr (ident.interp idc (x, y))
                                   | inr (x, inr y)
                                     => if Z.eqb y (2^Z.log2 y)
                                        then default_interp (ident.Z.shiftr (Z.log2 y)) x
                                        else default tt
                                   | _ => default tt
                                   end
                           | ident.Z_modulo as idc
                             => fun (x_y : _ * expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _))
                                => let default _ := default_interp idc x_y in
                                   match x_y return _ * expr _ + type.interp _ with
                                   | inr (inr x, inr y) => inr (ident.interp idc (x, y))
                                   | inr (x, inr y)
                                     => if Z.eqb y (2^Z.log2 y)
                                        then default_interp (ident.Z.land (y-1)) x
                                        else default tt
                                   | _ => default tt
                                   end
                           | ident.Z_mul as idc
                             => fun (x_y : _ * expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _))
                                => let default _ := default_interp idc x_y in
                                   match x_y return _ * expr _ + type.interp _ with
                                   | inr (inr x, inr y) => inr (ident.interp idc (x, y))
                                   | inr (inr x, inl (data, e) as y)
                                   | inr (inl (data, e) as y, inr x)
                                     => let data' _ := ZRange.ident.option.interp idc (data, Some r[x~>x]%zrange) in
                                        if Z.eqb x 0
                                        then inr 0%Z
                                        else if Z.eqb x 1
                                             then y
                                             else if Z.eqb x (-1)
                                                  then inl (data' tt, AppIdent ident.Z.opp (expr.reify (t:=type.Z) y))
                                                  else if Z.eqb x (2^Z.log2 x)
                                                       then inl (data' tt,
                                                                 AppIdent (ident.Z.shiftl (Z.log2 x)) (expr.reify (t:=type.Z) y))
                                                       else inl (data' tt,
                                                                 AppIdent idc (ident.primitive (t:=type.Z) x @@ TT, expr.reify (t:=type.Z) y))
                                   | inr (inl (dataa, a), inl (datab, b))
                                     => inl (ZRange.ident.option.interp idc (dataa, datab),
                                             AppIdent idc (a, b))
                                   | inl _ => default tt
                                   end
                           | ident.Z_add as idc
                             => fun (x_y : _ * expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _))
                                => let default0 _ := AppIdent idc (expr.reify (t:=_*_) x_y) in
                                   let default _ := expr.reflect (default0 tt) in
                                   match x_y return _ * expr _ + type.interp _ with
                                   | inr (inr x, inr y) => inr (ident.interp idc (x, y))
                                   | inr (inr x, inl (data, e) as y)
                                   | inr (inl (data, e) as y, inr x)
                                     => let data' _ := ZRange.ident.option.interp idc (data, Some r[x~>x]%zrange) in
                                        if Z.eqb x 0
                                        then y
                                        else inl (data' tt,
                                                  match invert_Z_opp e with
                                                  | Some e => AppIdent
                                                                ident.Z.sub
                                                                (ident.primitive (t:=type.Z) x @@ TT,
                                                                 e)
                                                  | None => default0 tt
                                                  end)
                                   | inr (inl (dataa, a), inl (datab, b))
                                     => inl (ZRange.ident.option.interp idc (dataa, datab),
                                             match invert_Z_opp a, invert_Z_opp b with
                                             | Some a, Some b
                                               => AppIdent
                                                    ident.Z.opp
                                                    (idc @@ (a, b))
                                             | Some a, None
                                               => AppIdent ident.Z.sub (b, a)
                                             | None, Some b
                                               => AppIdent ident.Z.sub (a, b)
                                             | None, None => default0 tt
                                             end)
                                   | inl _ => default tt
                                   end
                           | ident.Z_sub as idc
                             => fun (x_y : _ * expr (_ * _) + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _))
                                => let default0 _ := AppIdent idc (expr.reify (t:=_*_) x_y) in
                                   let default _ := expr.reflect (default0 tt) in
                                   match x_y return _ * expr _ + type.interp _ with
                                   | inr (inr x, inr y) => inr (ident.interp idc (x, y))
                                   | inr (inr x, inl (data, e))
                                     => let data' _ := ZRange.ident.option.interp idc (Some r[x~>x]%zrange, data) in
                                        if Z.eqb x 0
                                        then inl (data' tt, AppIdent ident.Z.opp e)
                                        else inl (data' tt, default0 tt)
                                   | inr (inl (data, e), inr x)
                                     => let data' _ := ZRange.ident.option.interp idc (data, Some r[x~>x]%zrange) in
                                        if Z.eqb x 0
                                        then inl (data' tt, e)
                                        else inl (data' tt, default0 tt)
                                   | inr (inl (dataa, a), inl (datab, b))
                                     => inl (ZRange.ident.option.interp idc (dataa, datab),
                                             match invert_Z_opp a, invert_Z_opp b with
                                             | Some a, Some b
                                               => AppIdent
                                                    ident.Z.opp
                                                    (idc @@ (a, b))
                                             | Some a, None
                                               => AppIdent ident.Z.add (b, a)
                                             | None, Some b
                                               => AppIdent ident.Z.add (a, b)
                                             | None, None => default0 tt
                                             end)
                                   | inl _ => default tt
                                   end
                           | ident.Z_cast r as idc
                             => fun (x : _ * expr _ + type.interp _)
                                => match x with
                                   | inr x => inr (ident.interp idc x)
                                   | inl (data, e)
                                     => inl (ZRange.ident.option.interp idc data, e)
                                   end
                           | ident.Z_cast2 (r1, r2) as idc
                             => fun (x : _ * expr _ + (_ * expr _ + type.interp _) * (_ * expr _ + type.interp _))
                                => match x with
                                   | inr (inr a, inr b)
                                     => inr (inr (ident.interp (ident.Z.cast r1) a),
                                             inr (ident.interp (ident.Z.cast r2) b))
                                   | inr (inr a, inl (r2', b))
                                     => inr (inr (ident.interp (ident.Z.cast r1) a),
                                             inl (ZRange.ident.option.interp (ident.Z.cast r2) r2', b))
                                   | inr (inl (r1', a), inr b)
                                     => inr (inl (ZRange.ident.option.interp (ident.Z.cast r1) r1', a),
                                             inr (ident.interp (ident.Z.cast r2) b))
                                   | inr (inl (r1', a), inl (r2', b))
                                     => inr (inl (ZRange.ident.option.interp (ident.Z.cast r1) r1', a),
                                             inl (ZRange.ident.option.interp (ident.Z.cast r2) r2', b))
                                   | inl (data, e)
                                     => inl (ZRange.ident.option.interp idc data, e)
                                   end
                           end.
                    End interp.

                    Section partial_evaluate.
                      Context (inline_var_nodes : bool)
                              {var : type -> Type}.

                      Definition partial_evaluate'_step
                                 (partial_evaluate' : forall {t} (e : @expr (partial.value var) t),
                                     partial.value var t)
                                 {t} (e : @expr (partial.value var) t)
                        : partial.value var t
                        := match e in expr.expr t return partial.value var t with
                           | Var t v => v
                           | TT => inr tt
                           | AppIdent s d idc args => partial.ident.interp inline_var_nodes idc (@partial_evaluate' _ args)
                           | Pair A B a b => inr (@partial_evaluate' A a, @partial_evaluate' B b)
                           | App s d f x => @partial_evaluate' _ f (@partial_evaluate' _ x)
                           | Abs s d f => fun x => @partial_evaluate' d (f x)
                           end.
                      Fixpoint partial_evaluate' {t} (e : @expr (partial.value var) t)
                        : partial.value var t
                        := @partial_evaluate'_step (@partial_evaluate') t e.

                      Definition partial_evaluate {t} (e : @expr (partial.value var) t) : @expr var t
                        := partial.expr.reify (@partial_evaluate' t e).

                    End partial_evaluate.

                    Definition PartialEvaluate (inline_var_nodes : bool) {t} (e : Expr t) : Expr t
                      := fun var => @partial_evaluate inline_var_nodes var t (e _).
                  End ident.
                End partial.
              End expr.
            End DefaultValue.
          End Uncurry.
        End expr.
      End canonicalize_list_recursion.
    End Uncurried.
  End Compilers.
End ZRange.
Import for_reification.Notations.Reification.
Import Coq.Lists.List.
Import ListNotations.
Open Scope list_scope.
Open Scope Z_scope.


Definition r := ltac:(let r := constr:(fun (n : nat) (ls : list Z) =>
                                         combine (map (fun i : nat => 2 ^ (- (- (51 * Z.of_nat i) / 2))) (seq 0 n))
                                                 (nat_rect (fun _ : nat => nat -> list Z) (fun _ : nat => [])
                                                           (fun (_ : nat) (rec_call : nat -> list Z) (idx : nat) =>
                                                              nth_default (-1) ls idx :: rec_call (S idx)) n 0%nat)) in
                      let r := Reify r in
                      exact r).
Definition e := Eval vm_compute in canonicalize_list_recursion r.

Definition k'
  := Eval vm_compute in
      CPS.CallFunWithIdContinuation
        (CPS.Translate
           (Uncurry
              (e @ Reify 10%nat)%Expr)).

Definition prek'' := Eval vm_compute in option_map ToFlat k'.
Definition k'' := Eval cbv in match prek'' as x return match x with Some _ => _ | _ => _ end with
                              | Some v => v
                              | None => I
                              end.

Definition ToFlatFromFlat_Fast (_ : unit) := ToFlat (FromFlat k'').
Definition ToFlatFFromFlat_Slow (_ : unit) := ToFlat (PartialEvaluate false (FromFlat k'')).

Definition Part1 (_ : unit) := FromFlat k''.
Definition ComputedPart1 := Eval vm_compute in Part1 tt.
Definition Part2 (_ : unit) := PartialEvaluate false (Part1 tt).
Definition Part2_Fast (_ : unit) := PartialEvaluate false ComputedPart1.
Definition Part1And2_SlowWhenComposed (_ : unit) := PartialEvaluate false (FromFlat k'').
(* We need inlining for OCaml extraction to work here *)
Definition Part3_Fast (_ : unit)
  := Eval cbv [Part2_Fast] in ToFlat (Part2_Fast tt).
Definition Part1And2And3_SlowWhenComposed (_ : unit)
  := Eval cbv [Part1And2_SlowWhenComposed] in ToFlat (Part1And2_SlowWhenComposed tt).
Time Eval vm_compute in Part3_Fast.
Time Eval vm_compute in Part1And2And3_SlowWhenComposed.
Axiom IO_unit : Set.
Axiom Return : forall t, t -> IO_unit.
Module All.
  Definition main := Return _ (Part3_Fast tt, Part1And2And3_SlowWhenComposed tt).
End All.
Module Fast.
  Definition main := Return _ (Part3_Fast tt).
End Fast.
Module Slow.
  Definition main := Return _ (Part1And2And3_SlowWhenComposed tt).
End Slow.
Module FlatAll.
  Definition main := Return _ (ToFlatFromFlat_Fast tt, ToFlatFFromFlat_Slow tt).
End FlatAll.
Module FlatFast.
  Definition main := Return _ (ToFlatFromFlat_Fast tt).
End FlatFast.
Module FlatSlow.
  Definition main := Return _ (ToFlatFFromFlat_Slow tt).
End FlatSlow.
Require Import Coq.extraction.Extraction.
Set Warnings Append "-extraction-opaque-accessed".
(*
Require Import Coq.extraction.ExtrHaskellBasic.
(* These brake things with missing Ord instances, so we don't import them
Require Import Coq.extraction.ExtrHaskellNatInt.
Require Import Coq.extraction.ExtrHaskellZInt.
Require Import Coq.extraction.ExtrHaskellNatNum.
Require Import Coq.extraction.ExtrHaskellZNum.*)
Extract Inlined Constant IO_unit => "GHC.Base.IO ()".
Extract Constant Return => "\ v -> return v GHC.Base.>> return ()".
Extraction Language Haskell.
Redirect "/tmp/slowsmall.hs" Recursive Extraction All.main.
Redirect "/tmp/slowsmallslow.hs" Recursive Extraction Slow.main.
Redirect "/tmp/slowsmallfast.hs" Recursive Extraction Fast.main.
Redirect "/tmp/slowsmallflat.hs" Recursive Extraction FlatAll.main.
Redirect "/tmp/slowsmallflatslow.hs" Recursive Extraction FlatSlow.main.
Redirect "/tmp/slowsmallflatfast.hs" Recursive Extraction FlatFast.main.
 *)
(*
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import Coq.extraction.ExtrOcamlNatInt.
Require Import Coq.extraction.ExtrOcamlZInt.
Extract Inlined Constant IO_unit => "()".
Extract Constant Return => "fun v -> ()".
Extraction Language OCaml.
Redirect "/tmp/slowsmall.ml" Recursive Extraction All.main.
Redirect "/tmp/slowsmallslow.ml" Recursive Extraction Slow.main.
Redirect "/tmp/slowsmallfast.ml" Recursive Extraction Fast.main.
Redirect "/tmp/slowsmallflat.ml" Recursive Extraction FlatAll.main.
Redirect "/tmp/slowsmallflatslow.ml" Recursive Extraction FlatSlow.main.
Redirect "/tmp/slowsmallflatfast.ml" Recursive Extraction FlatFast.main.
*)
