(** * Dead Code Elimination for PHOAS Syntax *)
Require Import Coq.Lists.List.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Util.Tactics Crypto.Util.Bool Crypto.Util.NatUtil.

Local Open Scope list_scope.
Local Open Scope ctype_scope.
Local Notation eta x := (fst x, snd x).
Section dead.
  Context (base_type_code : Type)
          (interp_base_type : base_type_code -> Type)
          (op : flat_type base_type_code -> flat_type base_type_code -> Type).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Let Tbase := @Tbase base_type_code.
  Local Coercion Tbase : base_type_code >-> Syntax.flat_type.
  Local Notation interp_type := (interp_type interp_base_type).
  Local Notation interp_flat_type := (interp_flat_type_gen interp_base_type).
  Local Notation exprf := (@exprf base_type_code interp_base_type op).
  Local Notation expr := (@expr base_type_code interp_base_type op).
  Local Notation Expr := (@Expr base_type_code interp_base_type op).

  Section with_var.
    Context {var : base_type_code -> Type}.
    Local Notation precpsvar t := (forall tC, (interp_flat_type_gen var t -> @exprf var tC) -> @exprf var tC).
    Local Notation cpsvar t := (forall tC, (interp_flat_type_gen var t -> @exprf var tC) -> @exprf var tC).
    Local Notation fcpsvar := (fun t : base_type_code => cpsvar t).

    Definition dead_code_eliminationf_step
               (dead_code_eliminationf : forall {t} (v : @exprf fcpsvar t), cpsvar t)
               {t} (v : @exprf fcpsvar t)
      : cpsvar t.
      refine match v in @Syntax.exprf _ _ _ _ t return cpsvar t with
             | Let _ ex _ eC
               => let ex' := @dead_code_eliminationf _ ex in
                 @dead_code_eliminationf _ (eC _)
             | _ => _
             end.
      Focus 4.
               => let '(vx,  := @find_live _ ex base in
                            @find_live _ (eC (SmartVal flvar (fun _ n => nat_beq n base || vx n)%bool _)) (S base)
             | _, _ => _
             end. let vx := @find_live _ ex base in
                            @find_live _ (eC (SmartVal flvar (fun _ n => nat_beq n base || vx n)%bool _)) (S base)
         | Const _ x => fun _ => false
         | Var _ x => x
         | Op _ _ op args => @find_live _ args base
         | Pair _ ex _ ey => let fx := @find_live _ ex base in
                             let fy := @find_live _ ey base in
                             fun n => (fx n || fy n)%bool
         end.

    Section with_var.
      Context {var : base_type_code -> Type}.
      Local Notation dvar t := (var t + interp_base_type t)%type.
      Local Notation fdvar := (fun t => dvar t).

  Section find_live.
    Local Notation lvart := (nat -> bool)%type.
    Local Notation lvar t := lvart (only parsing).
    Local Notation flvar := (fun _ : base_type_code => lvart).

    Definition find_live_step
               (find_live : forall {t} (v : @exprf flvar t) (base : nat), lvart)
               {t} (v : @exprf flvar t) (base : nat)
      : lvart
      := match v in @Syntax.exprf _ _ _ _ t return lvar t with
         | Let _ ex _ eC => let vx := @find_live _ ex base in
                            @find_live _ (eC (SmartVal flvar (fun _ n => nat_beq n base || vx n)%bool _)) (S base)
         | Const _ x => fun _ => false
         | Var _ x => x
         | Op _ _ op args => @find_live _ args base
         | Pair _ ex _ ey => let fx := @find_live _ ex base in
                             let fy := @find_live _ ey base in
                             fun n => (fx n || fy n)%bool
         end.

    Section with_var.
      Context {var : base_type_code -> Type}.
      Local Notation dvar t := (var t + interp_base_type t)%type.
      Local Notation fdvar := (fun t => dvar t).

      Definition elim_dead_step
                 (elim_dead : forall {t} (v : @exprf fvar t) (base : nat) (is_live : lvart), @exprf )
                 {t} (v : @exprf fdvar t) (base : nat)
        : @exprf var t
        := match v in @Syntax.exprf _ _ _ _ t return var t with
           | Let _ ex _ eC => let vx := @find_live _ ex base in
                              @find_live _ (eC (SmartVal fvar (fun _ n => nat_beq n base || vx n)%bool _)) (S base)
           | Const _ x => fun _ => false
           | Var _ x => x
           | Op _ _ op args => @find_live _ args base
           | Pair _ ex _ ey => let fx := @find_live _ ex base in
                               let fy := @find_live _ ey base in
                               fun n => (fx n || fy n)%bool
           end.

    Definition find_live csef {t} (v : @exprf fsvar t) (xs : mapping)
      := @csef_step (@csef) t v xs.



Focus 2.




  Section with_var.
    Context {var : base_type_code -> Type}.

    Local Notation svar t := (var t * nat)%type.
    Local Notation fsvar := (fun t => svar t).

    Context (prefix : list (sigT (fun t : flat_type => @exprf fsvar t))).



    Definition dcef_step
               (dcef : forall {t} (v : @exprf fsvar t) (base : nat), @exprf var t * list bool)
               {t} (v : @exprf fsvar t) (base : nat)
      : @exprf var t * list bool.
      refine match v in @Syntax.exprf _ _ _ _ t return exprf t * list bool with
             | Let tx ex _ eC => let '(lx, livex) := eta (@dcef _ ex base) in
                                (Let lx (
         | Const _ x => (Const x, repeat false base)
         | Var _ x => (Var (fst x), _)
         | Op _ _ op args => let '(largs, live) := eta (@dcef _ args base) in (Op op largs, live)
         | Pair _ ex _ ey => let '(lx, livex) := eta (@dcef _ ex base) in
                            let '(ly, livey) := eta (@dcef _ ey base) in
                            (Pair lx ly, _)
         end.

    Fixpoint csef {t} (v : @exprf fsvar t) (xs : mapping)
      := @csef_step (@csef) t v xs.



    Definition symbolize_smart_const {t} : interp_flat_type t -> symbolic_expr
      := smart_interp_flat_map base_type_code (g:=fun _ => symbolic_expr) (fun t v => SConst (symbolize_const t v)) (fun A B => SPair).

    Fixpoint symbolize_exprf
             {t} (v : @exprf fsvar t) {struct v}
      : option symbolic_expr
      := match v with
         | Const t x => Some (symbolize_smart_const x)
         | Var _ x => Some (snd x)
         | Op _ _ op args => option_map
                               (fun sargs => SOp (symbolize_op _ _ op) sargs)
                               (@symbolize_exprf _ args)
         | Let _ ex _ eC => None
         | Pair _ ex _ ey => match @symbolize_exprf _ ex, @symbolize_exprf _ ey with
                             | Some sx, Some sy => Some (SPair sx sy)
                             | _, _ => None
                             end
         end.

    Fixpoint smart_lookup_gen f (proj : forall t, svar t -> f t)
             (t : flat_type) (sv : symbolic_expr) (xs : mapping) {struct t}
      : option (interp_flat_type_gen f t)
      := match t return option (interp_flat_type_gen f t) with
         | Syntax.Tbase t => option_map (fun v => proj t (v, sv)) (lookup t sv xs)
         | Prod A B => match @smart_lookup_gen f proj A sv xs, @smart_lookup_gen f proj B sv xs with
                       | Some a, Some b => Some (a, b)
                       | _, _ => None
                       end
         end.
    Definition smart_lookup (t : flat_type) (sv : symbolic_expr) (xs : mapping) : option (interp_flat_type_gen fsvar t)
      := @smart_lookup_gen fsvar (fun _ x => x) t sv xs.
    Definition smart_lookupo (t : flat_type) (sv : option symbolic_expr) (xs : mapping) : option (interp_flat_type_gen fsvar t)
      := match sv with
         | Some sv => smart_lookup t sv xs
         | None => None
         end.
    Definition symbolicify_smart_var {t : flat_type} (xs : mapping) (replacement : option symbolic_expr)
      : interp_flat_type_gen var t -> interp_flat_type_gen fsvar t
      := smart_interp_flat_map
           (g:=interp_flat_type_gen fsvar)
           base_type_code (fun t v => (v,
                                       match replacement with
                                       | Some sv => sv
                                       | None => symbolicify_var v xs
                                       end))
           (fun A B => @pair _ _).
    Fixpoint smart_add_mapping {t : flat_type} (xs : mapping) : interp_flat_type_gen fsvar t -> mapping
      := match t return interp_flat_type_gen fsvar t -> mapping with
         | Syntax.Tbase t => fun v => add_mapping (fst v) (snd v) xs
         | Prod A B
           => fun v => let xs := @smart_add_mapping B xs (snd v) in
                       let xs := @smart_add_mapping A xs (fst v) in
                       xs
         end.

    Fixpoint prepend_prefix {t} (e : @exprf fsvar t) (ls : list (sigT (fun t : flat_type => @exprf fsvar t)))
      : @exprf fsvar t
      := match ls with
         | nil => e
         | x :: xs => Let (projT2 x) (fun _ => @prepend_prefix _ e xs)
         end.

    Fixpoint cse {t} (v : @expr fsvar t) (xs : mapping) {struct v} : @expr var t
      := match v in @Syntax.expr _ _ _ _ t return expr t with
         | Return _ x => Return (csef (prepend_prefix x prefix) xs)
         | Abs _ _ f => Abs (fun x => let x' := symbolicify_var x xs in
                                      @cse _ (f (x, x')) (add_mapping x x' xs))
         end.
  End with_var.

  Definition CSE {t} (e : Expr t) (prefix : forall var, list (sigT (fun t : flat_type => @exprf var t)))
    : Expr t
    := fun var => cse (prefix _) (e _) empty_mapping.
End symbolic.

Global Arguments csef {_} SConstT op_code base_type_code_beq SConstT_beq op_code_beq base_type_code_bl {_ _} symbolize_const symbolize_op {var t} _ _.
Global Arguments cse {_} SConstT op_code base_type_code_beq SConstT_beq op_code_beq base_type_code_bl {_ _} symbolize_const symbolize_op {var} prefix {t} _ _.
Global Arguments CSE {_} SConstT op_code base_type_code_beq SConstT_beq op_code_beq base_type_code_bl {_ _} symbolize_const symbolize_op {t} e prefix var.
