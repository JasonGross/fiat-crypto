Require Import Coq.ZArith.ZArith.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Crypto.Util.ListUtil Coq.Lists.List.
Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

Module Compilers.
  Export Language.Compilers.
  Import invert_expr.
  Import defaults.

  Module Subst01.
    Section with_counter.
      Context {t : Type}
              (one : t)
              (incr : t -> t)
              (add : t -> t -> t).

      Local Notation PositiveMap_incr idx m
        := (PositiveMap.add idx (match PositiveMap.find idx m with
                                 | Some n => incr n
                                 | None => one
                                 end) m).
      Local Notation PositiveMap_union m1 m2
        := (PositiveMap.map2
              (fun c1 c2
               => match c1, c2 with
                  | Some n1, Some n2 => Some (add n1 n2)
                  | Some n, None
                  | None, Some n
                    => Some n
                  | None, None => None
                  end) m1 m2).

      Section with_ident.
        Context {base_type : Type}.
        Local Notation type := (type.type base_type).
        Context {ident : type -> Type}.
        Local Notation expr := (@expr.expr base_type ident).
        Fixpoint compute_live_counts' {t} (e : @expr (fun _ => positive) t) (cur_idx : positive)
          : positive * PositiveMap.t _
          := match e with
             | expr.Var t v => (cur_idx, PositiveMap_incr v (PositiveMap.empty _))
             | expr.Ident t idc => (cur_idx, PositiveMap.empty _)
             | expr.App s d f x
               => let '(idx, live1) := @compute_live_counts' _ f cur_idx in
                  let '(idx, live2) := @compute_live_counts' _ x idx in
                  (idx, PositiveMap_union live1 live2)
             | expr.Abs s d f
               => let '(idx, live) := @compute_live_counts' _ (f cur_idx) (Pos.succ cur_idx) in
                  (cur_idx, live)
             | expr.LetIn tx tC ex eC
               => let '(idx, live1) := @compute_live_counts' tx ex cur_idx in
                  let '(idx', live2) := @compute_live_counts' tC (eC idx) (Pos.succ idx) in
                  (idx', if PositiveMap.mem idx live2
                         then PositiveMap_union live1 live2
                         else live2)
             end.
        Definition compute_live_counts {t} e : PositiveMap.t _ := snd (@compute_live_counts' t e 1).
        Definition ComputeLiveCounts {t} (e : expr.Expr t) := compute_live_counts (e _).

        Section with_var.
          Context (doing_subst : forall T1 T2, T1 -> T2 -> T1)
                  {var : type -> Type}
                  (should_subst : t -> bool)
                  (live : PositiveMap.t t).
          Fixpoint subst0n' {t} (e : @expr (@expr var) t) (cur_idx : positive)
            : positive * @expr var t
            := match e with
               | expr.Var t v => (cur_idx, v)
               | expr.Ident t idc => (cur_idx, expr.Ident idc)
               | expr.App s d f x
                 => let '(idx, f') := @subst0n' _ f cur_idx in
                    let '(idx, x') := @subst0n' _ x idx in
                    (idx, expr.App f' x')
               | expr.Abs s d f
                 => (cur_idx, expr.Abs (fun v => snd (@subst0n' _ (f (expr.Var v)) (Pos.succ cur_idx))))
               | expr.LetIn tx tC ex eC
                 => let '(idx, ex') := @subst0n' tx ex cur_idx in
                    let eC' := fun v => snd (@subst0n' tC (eC v) (Pos.succ idx)) in
                    if match PositiveMap.find idx live with
                       | Some n => should_subst n
                       | None => true
                       end
                    then (Pos.succ idx, eC' (doing_subst _ _ ex' (Pos.succ idx, PositiveMap.elements live)))
                    else (Pos.succ idx, expr.LetIn ex' (fun v => eC' (expr.Var v)))
               end.

          Definition subst0n {t} e : expr t
            := snd (@subst0n' t e 1).
        End with_var.

        Definition Subst0n (doing_subst : forall T1 T2, T1 -> T2 -> T1) (should_subst : t -> bool) {t} (e : expr.Expr t) : expr.Expr t
          := fun var => subst0n doing_subst should_subst (ComputeLiveCounts e) (e _).
      End with_ident.
    End with_counter.

    Section for_01.
      Inductive one_or_more := one | more.
      Local Notation t := one_or_more.
      Let incr : t -> t := fun _ => more.
      Let add : t -> t -> t := fun _ _ => more.
      Let should_subst : t -> bool
        := fun v => match v with
                    | one => true
                    | more => false
                    end.

      Definition Subst01 {base_type ident} {t} (e : expr.Expr t) : expr.Expr t
        := @Subst0n _ one incr add base_type ident (fun _ _ x _ => x) should_subst t e.
    End for_01.
  End Subst01.

  Module DeadCodeElimination.
    Section with_ident.
      Context {base_type : Type}.
      Local Notation type := (type.type base_type).
      Context {ident : type -> Type}.
      Local Notation expr := (@expr.expr base_type ident).

      Definition OUGHT_TO_BE_UNUSED {T1 T2} (v : T1) (v' : T2) := v.
      Global Opaque OUGHT_TO_BE_UNUSED.

      Definition EliminateDead {t} (e : expr.Expr t) : expr.Expr t
        := @Subst01.Subst0n unit tt (fun _ => tt) (fun _ _ => tt) base_type ident (@OUGHT_TO_BE_UNUSED) (fun _ => false) t e.
    End with_ident.
  End DeadCodeElimination.
End Compilers.
