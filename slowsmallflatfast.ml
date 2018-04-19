
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

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

(** val toFlatFromFlat_Fast :
    unit ->
    ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.Flat.expr **)

let toFlatFromFlat_Fast _ =
  ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.coq_ToFlat
    (ZRange.Compilers.Coq_type.Coq_arrow
    ((ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Coq_unit),
    (ZRange.Compilers.Coq_type.Coq_type_primitive
    ZRange.Compilers.Coq_type.Z))) (fun _ ->
    ZRange.Compilers.Uncurried.Coq_canonicalize_list_recursion.Coq_expr.Uncurry.DefaultValue.Coq_expr.coq_FromFlat
      (ZRange.Compilers.Coq_type.Coq_arrow
      ((ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Coq_unit),
      (ZRange.Compilers.Coq_type.Coq_type_primitive
      ZRange.Compilers.Coq_type.Z))) k'')

(** val return : 'a1 -> () **)

let return = fun v -> ()

module FlatFast =
 struct
  (** val main : () **)

  let main =
    return (toFlatFromFlat_Fast ())
 end

