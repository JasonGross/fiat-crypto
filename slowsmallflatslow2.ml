
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

(** val id : 'a1 -> 'a1 **)

let id x =
  x

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (_, h) -> h

module Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Pervasives.succ
 end

module PositiveMap =
 struct
  type key = int

  type 'a tree =
  | Leaf
  | Node of 'a tree * 'a option * 'a tree

  type 'a t = 'a tree

  (** val empty : 'a1 t **)

  let empty =
    Leaf

  (** val find : key -> 'a1 t -> 'a1 option **)

  let rec find i = function
  | Leaf -> None
  | Node (l, o, r) ->
    ((fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
       (fun ii -> find ii r)
       (fun ii -> find ii l)
       (fun _ -> o)
       i)

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec add i v = function
  | Leaf ->
    ((fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
       (fun ii -> Node (Leaf, None, (add ii v Leaf)))
       (fun ii -> Node ((add ii v Leaf), None, Leaf))
       (fun _ -> Node (Leaf, (Some v), Leaf))
       i)
  | Node (l, o, r) ->
    ((fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
       (fun ii -> Node (l, o, (add ii v r)))
       (fun ii -> Node ((add ii v l), o, r))
       (fun _ -> Node (l, (Some v), r))
       i)
 end

module Crypto_DOT_Util_DOT_Option =
 struct
  module Crypto =
   struct
    module Util =
     struct
      module Option =
       struct
        (** val bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option **)

        let bind v f =
          match v with
          | Some v0 -> f v0
          | None -> None
       end
     end
   end
 end

module Util =
 struct
  module ZRange =
   struct
    type zrange = { lower : int; upper : int }
   end
 end

module ZRange =
 struct
  module Compilers =
   struct
    module Coq_type =
     struct
      type primitive =
      | Coq_unit
      | Z
      | Coq_nat
      | Coq_bool

      type coq_type =
      | Coq_type_primitive of primitive
      | Coq_prod of coq_type * coq_type
      | Coq_arrow of coq_type * coq_type
      | Coq_list of coq_type

      type interp = __

      (** val try_transport : coq_type -> coq_type -> 'a1 -> 'a1 option **)

      let rec try_transport t1 t2 =
        match t1 with
        | Coq_type_primitive p ->
          (fun x ->
            match p with
            | Coq_unit ->
              (match t2 with
               | Coq_type_primitive p0 ->
                 (match p0 with
                  | Coq_unit -> Some x
                  | _ -> None)
               | _ -> None)
            | Z ->
              (match t2 with
               | Coq_type_primitive p0 ->
                 (match p0 with
                  | Z -> Some x
                  | _ -> None)
               | _ -> None)
            | Coq_nat ->
              (match t2 with
               | Coq_type_primitive p0 ->
                 (match p0 with
                  | Coq_nat -> Some x
                  | _ -> None)
               | _ -> None)
            | Coq_bool ->
              (match t2 with
               | Coq_type_primitive p0 ->
                 (match p0 with
                  | Coq_bool -> Some x
                  | _ -> None)
               | _ -> None))
        | Coq_prod (a, b) ->
          (fun x ->
            match t2 with
            | Coq_prod (a', b') ->
              Crypto_DOT_Util_DOT_Option.Crypto.Util.Option.bind
                (try_transport a a' x) (fun v -> try_transport b b' v)
            | _ -> None)
        | Coq_arrow (s, d) ->
          (fun x ->
            match t2 with
            | Coq_arrow (s', d') ->
              Crypto_DOT_Util_DOT_Option.Crypto.Util.Option.bind
                (try_transport s s' x) (fun v -> try_transport d d' v)
            | _ -> None)
        | Coq_list a ->
          (match t2 with
           | Coq_list a' -> try_transport a a'
           | _ -> (fun _ -> None))
     end
    module Coq__1 = Coq_type

    module Uncurried =
     struct
      module Coq_expr =
       struct
        type ('ident, 'var) expr =
        | Var of Coq_type.coq_type * 'var
        | TT
        | AppIdent of Coq_type.coq_type * Coq_type.coq_type * 'ident
           * ('ident, 'var) expr
        | App of Coq_type.coq_type * Coq_type.coq_type * ('ident, 'var) expr
           * ('ident, 'var) expr
        | Pair of Coq_type.coq_type * Coq_type.coq_type * ('ident, 'var) expr
           * ('ident, 'var) expr
        | Abs of Coq_type.coq_type * Coq_type.coq_type
           * ('var -> ('ident, 'var) expr)

        type 'ident coq_Expr = __ -> ('ident, __) expr

        module Coq_default =
         struct
          module Coq_ident =
           struct
            type ident =
            | Coq_primitive of Coq_type.primitive * Coq_type.interp
            | Let_In of Coq_type.coq_type * Coq_type.coq_type
            | Nat_succ
            | Nat_add
            | Nat_sub
            | Nat_mul
            | Nat_max
            | Coq_nil of Coq_type.coq_type
            | Coq_cons of Coq_type.coq_type
            | Coq_fst of Coq_type.coq_type * Coq_type.coq_type
            | Coq_snd of Coq_type.coq_type * Coq_type.coq_type
            | Coq_bool_rect of Coq_type.coq_type
            | Coq_nat_rect of Coq_type.coq_type
            | Coq_pred
            | Coq_list_rect of Coq_type.coq_type * Coq_type.coq_type
            | List_nth_default of Coq_type.coq_type
            | List_nth_default_concrete of Coq_type.primitive
               * Coq_type.interp * int
            | Z_shiftr of int
            | Z_shiftl of int
            | Z_land of int
            | Z_add
            | Z_mul
            | Z_pow
            | Z_sub
            | Z_opp
            | Z_div
            | Z_modulo
            | Z_eqb
            | Z_leb
            | Z_of_nat
            | Z_cast of Util.ZRange.zrange
            | Z_cast2 of (Util.ZRange.zrange * Util.ZRange.zrange)
           end
         end
       end

      module Coq_canonicalize_list_recursion =
       struct
        module Coq_expr =
         struct
          (** val invert_Pair :
              Coq_type.coq_type -> Coq_type.coq_type ->
              (Coq_expr.Coq_default.Coq_ident.ident, 'a1) Coq_expr.expr ->
              ((Coq_expr.Coq_default.Coq_ident.ident, 'a1)
              Coq_expr.expr * (Coq_expr.Coq_default.Coq_ident.ident, 'a1)
              Coq_expr.expr) option **)

          let invert_Pair _ _ = function
          | Coq_expr.Pair (_, _, a, b) -> Some (a, b)
          | _ -> None

          module Uncurry =
           struct
            module DefaultValue =
             struct
              module Coq_type =
               struct
                module Coq_primitive =
                 struct
                  (** val default : Coq_type.primitive -> Coq_type.interp **)

                  let default = function
                  | Coq_type.Coq_unit -> Obj.magic ()
                  | Coq_type.Z -> Obj.magic ((~-) 1)
                  | Coq_type.Coq_nat -> Obj.magic 0
                  | Coq_type.Coq_bool -> Obj.magic true
                 end
               end

              module Coq_expr =
               struct
                (** val default :
                    Coq__1.coq_type -> (Coq_expr.Coq_default.Coq_ident.ident,
                    'a1) Coq_expr.expr **)

                let rec default = function
                | Coq__1.Coq_type_primitive x ->
                  Coq_expr.AppIdent ((Coq__1.Coq_type_primitive
                    Coq__1.Coq_unit), (Coq__1.Coq_type_primitive x),
                    (Coq_expr.Coq_default.Coq_ident.Coq_primitive (x,
                    (Coq_type.Coq_primitive.default x))), Coq_expr.TT)
                | Coq__1.Coq_prod (a, b) ->
                  Coq_expr.Pair (a, b, (default a), (default b))
                | Coq__1.Coq_arrow (s, d) ->
                  Coq_expr.Abs (s, d, (fun _ -> default d))
                | Coq__1.Coq_list a ->
                  Coq_expr.AppIdent ((Coq__1.Coq_type_primitive
                    Coq__1.Coq_unit), (Coq__1.Coq_list a),
                    (Coq_expr.Coq_default.Coq_ident.Coq_nil a), Coq_expr.TT)

                module Flat =
                 struct
                  type expr =
                  | Var of Coq__1.coq_type * int
                  | TT
                  | AppIdent of Coq__1.coq_type * Coq__1.coq_type
                     * Coq_expr.Coq_default.Coq_ident.ident * expr
                  | App of Coq__1.coq_type * Coq__1.coq_type * expr * expr
                  | Pair of Coq__1.coq_type * Coq__1.coq_type * expr * expr
                  | Abs of Coq__1.coq_type * int * Coq__1.coq_type * expr
                 end

                (** val coq_ERROR : 'a1 -> 'a1 **)

                let coq_ERROR v =
                  v

                (** val to_flat' :
                    Coq__1.coq_type -> (Coq_expr.Coq_default.Coq_ident.ident,
                    PositiveMap.key) Coq_expr.expr -> PositiveMap.key ->
                    Flat.expr **)

                let rec to_flat' _ e cur_idx =
                  match e with
                  | Coq_expr.Var (t0, v) -> Flat.Var (t0, v)
                  | Coq_expr.TT -> Flat.TT
                  | Coq_expr.AppIdent (s, d, idc, args) ->
                    Flat.AppIdent (s, d, idc, (to_flat' s args cur_idx))
                  | Coq_expr.App (s, d, f, x) ->
                    Flat.App (s, d,
                      (to_flat' (Coq__1.Coq_arrow (s, d)) f cur_idx),
                      (to_flat' s x cur_idx))
                  | Coq_expr.Pair (a, b, a0, b0) ->
                    Flat.Pair (a, b, (to_flat' a a0 cur_idx),
                      (to_flat' b b0 cur_idx))
                  | Coq_expr.Abs (s, d, f) ->
                    Flat.Abs (s, cur_idx, d,
                      (to_flat' d (f cur_idx) (Pos.succ cur_idx)))

                (** val from_flat :
                    Coq__1.coq_type -> Flat.expr -> (Coq__1.coq_type, 'a1)
                    sigT PositiveMap.t ->
                    (Coq_expr.Coq_default.Coq_ident.ident, 'a1) Coq_expr.expr **)

                let rec from_flat _ e x =
                  match e with
                  | Flat.Var (t0, v) ->
                    (match Crypto_DOT_Util_DOT_Option.Crypto.Util.Option.bind
                             (PositiveMap.find v x) (fun tv ->
                             Coq__1.try_transport (projT1 tv) t0 (projT2 tv)) with
                     | Some v0 -> Coq_expr.Var (t0, v0)
                     | None -> coq_ERROR (default t0))
                  | Flat.TT -> Coq_expr.TT
                  | Flat.AppIdent (s, d, idc, args) ->
                    let args' = fun _ -> from_flat s args in
                    Coq_expr.AppIdent (s, d, idc, (args' __ x))
                  | Flat.App (s, d, f, x0) ->
                    let f' = fun _ -> from_flat (Coq__1.Coq_arrow (s, d)) f in
                    let x' = fun _ -> from_flat s x0 in
                    Coq_expr.App (s, d, (f' __ x), (x' __ x))
                  | Flat.Pair (a, b, a0, b0) ->
                    let a' = fun _ -> from_flat a a0 in
                    let b' = fun _ -> from_flat b b0 in
                    Coq_expr.Pair (a, b, (a' __ x), (b' __ x))
                  | Flat.Abs (s, cur_idx, d, f) ->
                    let f' = fun _ -> from_flat d f in
                    Coq_expr.Abs (s, d, (fun v ->
                    f' __ (PositiveMap.add cur_idx (ExistT (s, v)) x)))

                (** val to_flat :
                    Coq__1.coq_type -> (Coq_expr.Coq_default.Coq_ident.ident,
                    PositiveMap.key) Coq_expr.expr -> Flat.expr **)

                let to_flat t0 e =
                  to_flat' t0 e 1

                (** val coq_ToFlat :
                    Coq__1.coq_type -> Coq_expr.Coq_default.Coq_ident.ident
                    Coq_expr.coq_Expr -> Flat.expr **)

                let coq_ToFlat t0 e =
                  to_flat t0 (Obj.magic e __)

                (** val coq_FromFlat :
                    Coq__1.coq_type -> Flat.expr ->
                    (Coq_expr.Coq_default.Coq_ident.ident, 'a1) Coq_expr.expr **)

                let coq_FromFlat t0 e =
                  from_flat t0 e PositiveMap.empty
               end
             end
           end
         end
       end
     end
   end
 end

type 'var value = __

(** val reify :
    ZRange.Compilers.Coq_type.coq_type -> 'a1 value ->
    (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.ident, 'a1)
    ZRange.Compilers.Uncurried.Coq_expr.expr **)

let rec reify = function
| ZRange.Compilers.Coq_type.Coq_type_primitive p ->
  (fun v ->
    match Obj.magic v with
    | Inl e -> e
    | Inr v0 ->
      ZRange.Compilers.Uncurried.Coq_expr.AppIdent
        ((ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_unit),
        (ZRange.Compilers.Coq_type.Coq_type_primitive p),
        (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_primitive
        (p, v0)), ZRange.Compilers.Uncurried.Coq_expr.TT))
| ZRange.Compilers.Coq_type.Coq_prod (a, b) ->
  (fun v ->
    match Obj.magic v with
    | Inl e -> e
    | Inr p ->
      let (a0, b0) = p in
      ZRange.Compilers.Uncurried.Coq_expr.Pair (a, b, (reify a a0),
      (reify b b0)))
| ZRange.Compilers.Coq_type.Coq_arrow (s, d) ->
  (fun f -> ZRange.Compilers.Uncurried.Coq_expr.Abs (s, d, (fun v ->
    reify d
      (Obj.magic f
        (reflect s (ZRange.Compilers.Uncurried.Coq_expr.Var (s, v)))))))
| ZRange.Compilers.Coq_type.Coq_list _ -> Obj.magic id

(** val reflect :
    ZRange.Compilers.Coq_type.coq_type ->
    (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.ident, 'a1)
    ZRange.Compilers.Uncurried.Coq_expr.expr -> 'a1 value **)

and reflect = function
| ZRange.Compilers.Coq_type.Coq_type_primitive _ ->
  (fun v -> Obj.magic (Inl v))
| ZRange.Compilers.Coq_type.Coq_prod (a, b) ->
  (fun v ->
    match ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.invert_Pair
            a b v with
    | Some p ->
      let (a0, b0) = p in Obj.magic (Inr ((reflect a a0), (reflect b b0)))
    | None -> Obj.magic (Inl v))
| ZRange.Compilers.Coq_type.Coq_arrow (s, d) ->
  (fun f ->
    Obj.magic (fun v ->
      reflect d (ZRange.Compilers.Uncurried.Coq_expr.App (s, d, f,
        (reify s v)))))
| ZRange.Compilers.Coq_type.Coq_list _ -> Obj.magic id

(** val red'_ident2 :
    ZRange.Compilers.Coq_type.coq_type -> ZRange.Compilers.Coq_type.coq_type
    -> ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.ident -> 'a1
    value -> 'a1 value **)

let red'_ident2 _ _ = function
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_primitive (
    _, v) ->
  (fun _ -> Obj.magic (Inr v))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Let_In (tx, tC) ->
  (fun v ->
    reflect tC (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_prod (tx,
      (ZRange.Compilers.Coq_type.Coq_arrow (tx, tC)))), tC,
      (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Let_In (tx,
      tC)),
      (reify (ZRange.Compilers.Coq_type.Coq_prod (tx,
        (ZRange.Compilers.Coq_type.Coq_arrow (tx, tC)))) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Nat_succ ->
  (fun v ->
    match Obj.magic v with
    | Inl _ ->
      reflect (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_nat)
        (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
        ((ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_nat),
        (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_nat),
        ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Nat_succ,
        (reify (ZRange.Compilers.Coq_type.Coq_type_primitive
          ZRange.Compilers.Coq_type.Coq_nat) v)))
    | Inr v0 -> Obj.magic (Inr (Pervasives.succ v0)))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Nat_add ->
  (fun v ->
    reflect (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_nat)
      (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_prod
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_nat),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_nat))),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_nat),
      ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Nat_add,
      (reify (ZRange.Compilers.Coq_type.Coq_prod
        ((ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_nat),
        (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_nat))) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Nat_sub ->
  (fun v ->
    reflect (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_nat)
      (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_prod
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_nat),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_nat))),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_nat),
      ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Nat_sub,
      (reify (ZRange.Compilers.Coq_type.Coq_prod
        ((ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_nat),
        (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_nat))) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Nat_mul ->
  (fun v ->
    reflect (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_nat)
      (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_prod
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_nat),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_nat))),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_nat),
      ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Nat_mul,
      (reify (ZRange.Compilers.Coq_type.Coq_prod
        ((ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_nat),
        (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_nat))) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Nat_max ->
  (fun v ->
    reflect (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_nat)
      (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_prod
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_nat),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_nat))),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_nat),
      ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Nat_max,
      (reify (ZRange.Compilers.Coq_type.Coq_prod
        ((ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_nat),
        (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_nat))) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_nil t0 ->
  (fun v ->
    reflect (ZRange.Compilers.Coq_type.Coq_list t0)
      (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_unit),
      (ZRange.Compilers.Coq_type.Coq_list t0),
      (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_nil t0),
      (reify (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_unit) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_cons t0 ->
  (fun v ->
    reflect (ZRange.Compilers.Coq_type.Coq_list t0)
      (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_prod (t0,
      (ZRange.Compilers.Coq_type.Coq_list t0))),
      (ZRange.Compilers.Coq_type.Coq_list t0),
      (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_cons
      t0),
      (reify (ZRange.Compilers.Coq_type.Coq_prod (t0,
        (ZRange.Compilers.Coq_type.Coq_list t0))) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_fst (a, b) ->
  (fun v ->
    match Obj.magic v with
    | Inl _ ->
      reflect a (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
        ((ZRange.Compilers.Coq_type.Coq_prod (a, b)), a,
        (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_fst
        (a, b)), (reify (ZRange.Compilers.Coq_type.Coq_prod (a, b)) v)))
    | Inr p -> let (a0, _) = p in a0)
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_snd (a, b) ->
  (fun v ->
    match Obj.magic v with
    | Inl _ ->
      reflect b (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
        ((ZRange.Compilers.Coq_type.Coq_prod (a, b)), b,
        (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_snd
        (a, b)), (reify (ZRange.Compilers.Coq_type.Coq_prod (a, b)) v)))
    | Inr p -> let (_, b0) = p in b0)
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_bool_rect t0 ->
  (fun v ->
    reflect t0 (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_prod
      ((ZRange.Compilers.Coq_type.Coq_prod
      ((ZRange.Compilers.Coq_type.Coq_arrow
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_unit), t0)),
      (ZRange.Compilers.Coq_type.Coq_arrow
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_unit), t0)))),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_bool))), t0,
      (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_bool_rect
      t0),
      (reify (ZRange.Compilers.Coq_type.Coq_prod
        ((ZRange.Compilers.Coq_type.Coq_prod
        ((ZRange.Compilers.Coq_type.Coq_arrow
        ((ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_unit), t0)),
        (ZRange.Compilers.Coq_type.Coq_arrow
        ((ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_unit), t0)))),
        (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_bool))) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_nat_rect p ->
  let idc0 =
    ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_nat_rect p
  in
  (fun v ->
  match Obj.magic v with
  | Inl _ ->
    reflect p (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_prod
      ((ZRange.Compilers.Coq_type.Coq_prod
      ((ZRange.Compilers.Coq_type.Coq_arrow
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_unit), p)),
      (ZRange.Compilers.Coq_type.Coq_arrow
      ((ZRange.Compilers.Coq_type.Coq_prod
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_nat), p)), p)))),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_nat))), p, idc0,
      (reify (ZRange.Compilers.Coq_type.Coq_prod
        ((ZRange.Compilers.Coq_type.Coq_prod
        ((ZRange.Compilers.Coq_type.Coq_arrow
        ((ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_unit), p)),
        (ZRange.Compilers.Coq_type.Coq_arrow
        ((ZRange.Compilers.Coq_type.Coq_prod
        ((ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_nat), p)), p)))),
        (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_nat))) v)))
  | Inr p0 ->
    let (s, s0) = p0 in
    (match s with
     | Inl _ ->
       reflect p (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
         ((ZRange.Compilers.Coq_type.Coq_prod
         ((ZRange.Compilers.Coq_type.Coq_prod
         ((ZRange.Compilers.Coq_type.Coq_arrow
         ((ZRange.Compilers.Coq_type.Coq_type_primitive
         ZRange.Compilers.Coq_type.Coq_unit), p)),
         (ZRange.Compilers.Coq_type.Coq_arrow
         ((ZRange.Compilers.Coq_type.Coq_prod
         ((ZRange.Compilers.Coq_type.Coq_type_primitive
         ZRange.Compilers.Coq_type.Coq_nat), p)), p)))),
         (ZRange.Compilers.Coq_type.Coq_type_primitive
         ZRange.Compilers.Coq_type.Coq_nat))), p, idc0,
         (reify (ZRange.Compilers.Coq_type.Coq_prod
           ((ZRange.Compilers.Coq_type.Coq_prod
           ((ZRange.Compilers.Coq_type.Coq_arrow
           ((ZRange.Compilers.Coq_type.Coq_type_primitive
           ZRange.Compilers.Coq_type.Coq_unit), p)),
           (ZRange.Compilers.Coq_type.Coq_arrow
           ((ZRange.Compilers.Coq_type.Coq_prod
           ((ZRange.Compilers.Coq_type.Coq_type_primitive
           ZRange.Compilers.Coq_type.Coq_nat), p)), p)))),
           (ZRange.Compilers.Coq_type.Coq_type_primitive
           ZRange.Compilers.Coq_type.Coq_nat))) v)))
     | Inr p1 ->
       let (n, c) = p1 in
       (match s0 with
        | Inl _ ->
          reflect p (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
            ((ZRange.Compilers.Coq_type.Coq_prod
            ((ZRange.Compilers.Coq_type.Coq_prod
            ((ZRange.Compilers.Coq_type.Coq_arrow
            ((ZRange.Compilers.Coq_type.Coq_type_primitive
            ZRange.Compilers.Coq_type.Coq_unit), p)),
            (ZRange.Compilers.Coq_type.Coq_arrow
            ((ZRange.Compilers.Coq_type.Coq_prod
            ((ZRange.Compilers.Coq_type.Coq_type_primitive
            ZRange.Compilers.Coq_type.Coq_nat), p)), p)))),
            (ZRange.Compilers.Coq_type.Coq_type_primitive
            ZRange.Compilers.Coq_type.Coq_nat))), p, idc0,
            (reify (ZRange.Compilers.Coq_type.Coq_prod
              ((ZRange.Compilers.Coq_type.Coq_prod
              ((ZRange.Compilers.Coq_type.Coq_arrow
              ((ZRange.Compilers.Coq_type.Coq_type_primitive
              ZRange.Compilers.Coq_type.Coq_unit), p)),
              (ZRange.Compilers.Coq_type.Coq_arrow
              ((ZRange.Compilers.Coq_type.Coq_prod
              ((ZRange.Compilers.Coq_type.Coq_type_primitive
              ZRange.Compilers.Coq_type.Coq_nat), p)), p)))),
              (ZRange.Compilers.Coq_type.Coq_type_primitive
              ZRange.Compilers.Coq_type.Coq_nat))) v)))
        | Inr n0 ->
          let rec f n1 =
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> n (Inr ()))
              (fun n2 -> c (Inr ((Inr n2), (f n2))))
              n1
          in f n0)))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_pred ->
  (fun v ->
    reflect (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_nat)
      (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_nat),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_nat),
      ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_pred,
      (reify (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_nat) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_list_rect (
    a, p) ->
  (fun v ->
    reflect p (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_prod
      ((ZRange.Compilers.Coq_type.Coq_prod
      ((ZRange.Compilers.Coq_type.Coq_arrow
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_unit), p)),
      (ZRange.Compilers.Coq_type.Coq_arrow
      ((ZRange.Compilers.Coq_type.Coq_prod
      ((ZRange.Compilers.Coq_type.Coq_prod (a,
      (ZRange.Compilers.Coq_type.Coq_list a))),
      (ZRange.Compilers.Coq_type.Coq_arrow
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_unit), p)))), p)))),
      (ZRange.Compilers.Coq_type.Coq_list a))), p,
      (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_list_rect
      (a, p)),
      (reify (ZRange.Compilers.Coq_type.Coq_prod
        ((ZRange.Compilers.Coq_type.Coq_prod
        ((ZRange.Compilers.Coq_type.Coq_arrow
        ((ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_unit), p)),
        (ZRange.Compilers.Coq_type.Coq_arrow
        ((ZRange.Compilers.Coq_type.Coq_prod
        ((ZRange.Compilers.Coq_type.Coq_prod (a,
        (ZRange.Compilers.Coq_type.Coq_list a))),
        (ZRange.Compilers.Coq_type.Coq_arrow
        ((ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_unit), p)))), p)))),
        (ZRange.Compilers.Coq_type.Coq_list a))) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.List_nth_default t0 ->
  (fun v ->
    reflect t0 (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_prod
      ((ZRange.Compilers.Coq_type.Coq_prod (t0,
      (ZRange.Compilers.Coq_type.Coq_list t0))),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_nat))), t0,
      (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.List_nth_default
      t0),
      (reify (ZRange.Compilers.Coq_type.Coq_prod
        ((ZRange.Compilers.Coq_type.Coq_prod (t0,
        (ZRange.Compilers.Coq_type.Coq_list t0))),
        (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_nat))) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.List_nth_default_concrete (
    t0, d, n) ->
  (fun v ->
    reflect (ZRange.Compilers.Coq_type.Coq_type_primitive t0)
      (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_list
      (ZRange.Compilers.Coq_type.Coq_type_primitive t0)),
      (ZRange.Compilers.Coq_type.Coq_type_primitive t0),
      (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.List_nth_default_concrete
      (t0, d, n)),
      (reify (ZRange.Compilers.Coq_type.Coq_list
        (ZRange.Compilers.Coq_type.Coq_type_primitive t0)) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_shiftr offset ->
  (fun v ->
    reflect (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z)
      (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_shiftr
      offset),
      (reify (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Z) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_shiftl offset ->
  (fun v ->
    reflect (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z)
      (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_shiftl
      offset),
      (reify (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Z) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_land mask ->
  (fun v ->
    reflect (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z)
      (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_land
      mask),
      (reify (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Z) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_add ->
  (fun v ->
    reflect (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z)
      (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_prod
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z))),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_add,
      (reify (ZRange.Compilers.Coq_type.Coq_prod
        ((ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Z),
        (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Z))) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_mul ->
  (fun v ->
    reflect (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z)
      (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_prod
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z))),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_mul,
      (reify (ZRange.Compilers.Coq_type.Coq_prod
        ((ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Z),
        (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Z))) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_pow ->
  (fun v ->
    reflect (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z)
      (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_prod
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z))),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_pow,
      (reify (ZRange.Compilers.Coq_type.Coq_prod
        ((ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Z),
        (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Z))) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_sub ->
  (fun v ->
    reflect (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z)
      (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_prod
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z))),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_sub,
      (reify (ZRange.Compilers.Coq_type.Coq_prod
        ((ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Z),
        (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Z))) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_opp ->
  (fun v ->
    reflect (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z)
      (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_opp,
      (reify (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Z) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_div ->
  (fun v ->
    reflect (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z)
      (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_prod
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z))),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_div,
      (reify (ZRange.Compilers.Coq_type.Coq_prod
        ((ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Z),
        (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Z))) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_modulo ->
  (fun v ->
    reflect (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z)
      (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_prod
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z))),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_modulo,
      (reify (ZRange.Compilers.Coq_type.Coq_prod
        ((ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Z),
        (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Z))) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_eqb ->
  (fun v ->
    reflect (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_bool)
      (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_prod
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z))),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_bool),
      ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_eqb,
      (reify (ZRange.Compilers.Coq_type.Coq_prod
        ((ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Z),
        (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Z))) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_leb ->
  (fun v ->
    reflect (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_bool)
      (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_prod
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z))),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_bool),
      ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_leb,
      (reify (ZRange.Compilers.Coq_type.Coq_prod
        ((ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Z),
        (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Z))) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_of_nat ->
  (fun v ->
    reflect (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z)
      (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_nat),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_of_nat,
      (reify (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_nat) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_cast range ->
  (fun v ->
    reflect (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z)
      (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_cast
      range),
      (reify (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Z) v))))
| ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_cast2 range ->
  (fun v ->
    reflect (ZRange.Compilers.Coq_type.Coq_prod
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z)))
      (ZRange.Compilers.Uncurried.Coq_expr.AppIdent
      ((ZRange.Compilers.Coq_type.Coq_prod
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z))), (ZRange.Compilers.Coq_type.Coq_prod
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z))),
      (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Z_cast2
      range),
      (reify (ZRange.Compilers.Coq_type.Coq_prod
        ((ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Z),
        (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Z))) v))))

(** val red' :
    (ZRange.Compilers.Coq_type.coq_type -> ZRange.Compilers.Coq_type.coq_type
    -> ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.ident -> 'a1
    value -> 'a1 value) -> ZRange.Compilers.Coq_type.coq_type ->
    (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.ident, 'a1
    value) ZRange.Compilers.Uncurried.Coq_expr.expr -> 'a1 value **)

let rec red' red'_ident _ = function
| ZRange.Compilers.Uncurried.Coq_expr.Var (_, v) -> v
| ZRange.Compilers.Uncurried.Coq_expr.TT -> Obj.magic (Inr ())
| ZRange.Compilers.Uncurried.Coq_expr.AppIdent (s, d, idc, args) ->
  red'_ident s d idc (red' red'_ident s args)
| ZRange.Compilers.Uncurried.Coq_expr.App (s, d, f, x) ->
  Obj.magic red' red'_ident (ZRange.Compilers.Coq_type.Coq_arrow (s, d)) f
    (red' red'_ident s x)
| ZRange.Compilers.Uncurried.Coq_expr.Pair (a, b, a0, b0) ->
  Obj.magic (Inr ((red' red'_ident a a0), (red' red'_ident b b0)))
| ZRange.Compilers.Uncurried.Coq_expr.Abs (_, d, f) ->
  Obj.magic (fun v -> red' red'_ident d (f v))

(** val red2 :
    ZRange.Compilers.Coq_type.coq_type ->
    ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.ident
    ZRange.Compilers.Uncurried.Coq_expr.coq_Expr ->
    (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.ident, 'a1)
    ZRange.Compilers.Uncurried.Coq_expr.expr **)

let red2 t0 e =
  reify t0 (red' red'_ident2 t0 (e __))

(** val k'' :
    ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.expr **)

let k'' =
  ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Abs
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_unit), 1,
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.App
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.AppIdent
    ((ZRange.Compilers.Coq_type.Coq_prod ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_unit), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat))),
    (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_nat_rect
    (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z)))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Pair
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_unit), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Pair
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_unit), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Abs
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_unit), ((fun p->2*p) 1),
    (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Abs
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))), ((fun p->1+2*p) 1),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.App
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Var
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))), ((fun p->1+2*p) 1))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Abs
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), ((fun p->2*p) ((fun p->2*p) 1)),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.App
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.AppIdent
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_snd
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Var
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), ((fun p->2*p) ((fun p->2*p) 1)))))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.AppIdent
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_unit),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_primitive
    (ZRange.Compilers.Coq_type.Z, (Obj.magic 0))),
    ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.TT)))))))))))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Abs
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), ((fun p->2*p) 1),
    (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Abs
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))), ((fun p->1+2*p) 1),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.App
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.AppIdent
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_snd
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Var
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), ((fun p->2*p) 1))))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Abs
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))), ((fun p->2*p) ((fun p->2*p) 1)),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.App
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Var
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))), ((fun p->1+2*p) 1))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Abs
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), ((fun p->1+2*p) ((fun p->2*p) 1)),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.App
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.AppIdent
    ((ZRange.Compilers.Coq_type.Coq_prod ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_unit), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat))),
    (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_nat_rect
    (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z)))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Pair
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_unit), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Pair
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_unit), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Abs
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_unit), ((fun p->2*p) ((fun p->1+2*p) 1)),
    (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Abs
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))), ((fun p->1+2*p) ((fun p->1+2*p) 1)),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.App
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Var
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))), ((fun p->1+2*p) ((fun p->1+2*p) 1)))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.AppIdent
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_unit),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_primitive
    (ZRange.Compilers.Coq_type.Z, (Obj.magic 0))),
    ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.TT)))))))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Abs
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), ((fun p->2*p) ((fun p->1+2*p) 1)),
    (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Abs
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))), ((fun p->1+2*p) ((fun p->1+2*p) 1)),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.App
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.AppIdent
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_snd
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Var
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), ((fun p->2*p) ((fun p->1+2*p) 1)))))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Abs
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z), ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    1))), (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.App
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Var
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))), ((fun p->2*p) ((fun p->2*p) 1)))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Pair
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.AppIdent
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat),
    (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_fst
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Var
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), ((fun p->2*p) ((fun p->1+2*p) 1)))))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Abs
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z), ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
    1))), (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.App
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Var
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))), ((fun p->1+2*p) ((fun p->1+2*p) 1)))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Var
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z), ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
    1))))))))))))))))))))))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.AppIdent
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat),
    (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_fst
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Var
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), ((fun p->1+2*p) ((fun p->2*p)
    1)))))))))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Abs
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z), ((fun p->2*p) ((fun p->1+2*p) 1)),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.App
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.AppIdent
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_snd
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Var
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))), ((fun p->1+2*p) ((fun p->2*p) 1)))))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Var
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z), ((fun p->2*p) ((fun p->1+2*p)
    1)))))))))))))))))))))))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.AppIdent
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_unit),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat),
    (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_primitive
    (ZRange.Compilers.Coq_type.Coq_nat,
    (Obj.magic (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))),
    ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.TT)))))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Abs
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))), ((fun p->2*p) 1),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.App
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Var
    ((ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_prod
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))))),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))), ((fun p->2*p) 1))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Pair
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat), (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.AppIdent
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_unit),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_nat),
    (ZRange.Compilers.Uncurried.Coq_expr.Coq_default.Coq_ident.Coq_primitive
    (ZRange.Compilers.Coq_type.Coq_nat,
    (Obj.magic (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))),
    ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.TT)),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Abs
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z), ((fun p->1+2*p) 1),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z),
    (ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.Var
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z), ((fun p->1+2*p) 1))))))))))))))

(** val toFlatFFromFlat_Slow2 :
    unit ->
    ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.expr **)

let toFlatFFromFlat_Slow2 _ =
  ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.coq_ToFlat
    (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_unit),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))) (fun _ ->
    red2 (ZRange.Compilers.Coq_type.Coq_arrow
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_unit),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z))) (fun _ ->
      ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.coq_FromFlat
        (ZRange.Compilers.Coq_type.Coq_arrow
        ((ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Coq_unit),
        (ZRange.Compilers.Coq_type.Coq_type_primitive
        ZRange.Compilers.Coq_type.Z))) k''))

(** val return : 'a1 -> () **)

let return = fun v -> ()

module FlatSlow2 =
 struct
  (** val main : () **)

  let main =
    return (toFlatFFromFlat_Slow2 ())
 end

