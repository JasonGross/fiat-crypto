
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let app x =
  let rec app0 l m =
    match l with
    | [] -> m
    | a :: l1 -> a :: (app0 l1 m)
  in app0 x

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let iter f =
    let rec iter_fix x = function
    | XI n' -> f (iter_fix (iter_fix x n') n')
    | XO n' -> iter_fix (iter_fix x n') n'
    | XH -> f x
    in iter_fix

  (** val size : positive -> positive **)

  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XI _ -> Lt
             | XO _ -> Lt
             | XH -> r)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | XO _ -> false
                | XH -> false)
    | XO p0 -> (match q with
                | XI _ -> false
                | XO q0 -> eqb p0 q0
                | XH -> false)
    | XH -> (match q with
             | XI _ -> false
             | XO _ -> false
             | XH -> true)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module N =
 struct
  (** val of_nat : nat -> n **)

  let of_nat = function
  | O -> N0
  | S n' -> Npos (Pos.of_succ_nat n')
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val succ : z -> z **)

  let succ x =
    add x (Zpos XH)

  (** val pred : z -> z **)

  let pred x =
    add x (Zneg XH)

  (** val sub : z -> z -> z **)

  let sub m n0 =
    add m (opp n0)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val pow_pos : z -> positive -> z **)

  let pow_pos z0 =
    Pos.iter (mul z0) (Zpos XH)

  (** val pow : z -> z -> z **)

  let pow x = function
  | Z0 -> Zpos XH
  | Zpos p -> pow_pos x p
  | Zneg _ -> Z0

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' ->
      (match y with
       | Z0 -> Gt
       | Zpos y' -> Pos.compare x' y'
       | Zneg _ -> Gt)
    | Zneg x' ->
      (match y with
       | Z0 -> Lt
       | Zpos _ -> Lt
       | Zneg y' -> compOpp (Pos.compare x' y'))

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Eq -> true
    | Lt -> true
    | Gt -> false

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Eq -> false
    | Lt -> true
    | Gt -> false

  (** val eqb : z -> z -> bool **)

  let rec eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | Zpos _ -> false
             | Zneg _ -> false)
    | Zpos p ->
      (match y with
       | Z0 -> false
       | Zpos q -> Pos.eqb p q
       | Zneg _ -> false)
    | Zneg p ->
      (match y with
       | Z0 -> false
       | Zpos _ -> false
       | Zneg q -> Pos.eqb p q)

  (** val abs : z -> z **)

  let abs = function
  | Z0 -> Z0
  | Zpos p -> Zpos p
  | Zneg p -> Zpos p

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n1 -> Zpos (Pos.of_succ_nat n1)

  (** val log2 : z -> z **)

  let log2 = function
  | Z0 -> Z0
  | Zpos p0 ->
    (match p0 with
     | XI p -> Zpos (Pos.size p)
     | XO p -> Zpos (Pos.size p)
     | XH -> Z0)
  | Zneg _ -> Z0

  (** val log2_up : z -> z **)

  let log2_up a =
    match compare (Zpos XH) a with
    | Eq -> Z0
    | Lt -> succ (log2 (pred a))
    | Gt -> Z0
 end

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

module HexString =
 struct
  module Raw =
   struct
    (** val of_pos : positive -> char list -> char list **)

    let rec of_pos p rest =
      match p with
      | XI p0 ->
        (match p0 with
         | XI p1 ->
           (match p1 with
            | XI p2 ->
              (match p2 with
               | XI p' -> of_pos p' ('f'::rest)
               | XO p' -> of_pos p' ('7'::rest)
               | XH -> 'f'::rest)
            | XO p2 ->
              (match p2 with
               | XI p' -> of_pos p' ('b'::rest)
               | XO p' -> of_pos p' ('3'::rest)
               | XH -> 'b'::rest)
            | XH -> '7'::rest)
         | XO p1 ->
           (match p1 with
            | XI p2 ->
              (match p2 with
               | XI p' -> of_pos p' ('d'::rest)
               | XO p' -> of_pos p' ('5'::rest)
               | XH -> 'd'::rest)
            | XO p2 ->
              (match p2 with
               | XI p' -> of_pos p' ('9'::rest)
               | XO p' -> of_pos p' ('1'::rest)
               | XH -> '9'::rest)
            | XH -> '5'::rest)
         | XH -> '3'::rest)
      | XO p0 ->
        (match p0 with
         | XI p1 ->
           (match p1 with
            | XI p2 ->
              (match p2 with
               | XI p' -> of_pos p' ('e'::rest)
               | XO p' -> of_pos p' ('6'::rest)
               | XH -> 'e'::rest)
            | XO p2 ->
              (match p2 with
               | XI p' -> of_pos p' ('a'::rest)
               | XO p' -> of_pos p' ('2'::rest)
               | XH -> 'a'::rest)
            | XH -> '6'::rest)
         | XO p1 ->
           (match p1 with
            | XI p2 ->
              (match p2 with
               | XI p' -> of_pos p' ('c'::rest)
               | XO p' -> of_pos p' ('4'::rest)
               | XH -> 'c'::rest)
            | XO p2 ->
              (match p2 with
               | XI p' -> of_pos p' ('8'::rest)
               | XO p' -> of_pos p' ('0'::rest)
               | XH -> '8'::rest)
            | XH -> '4'::rest)
         | XH -> '2'::rest)
      | XH -> '1'::rest
   end

  (** val of_pos : positive -> char list **)

  let of_pos p =
    '0'::('x'::(Raw.of_pos p []))

  (** val of_Z : z -> char list **)

  let of_Z = function
  | Z0 -> '0'::('x'::('0'::[]))
  | Zpos p -> of_pos p
  | Zneg p -> '-'::(of_pos p)

  type uint =
  | Nil
  | D0 of uint
  | D1 of uint
  | D2 of uint
  | D3 of uint
  | D4 of uint
  | D5 of uint
  | D6 of uint
  | D7 of uint
  | D8 of uint
  | D9 of uint

  (** val revapp : uint -> uint -> uint **)

  let rec revapp d d' =
    match d with
    | Nil -> d'
    | D0 d0 -> revapp d0 (D0 d')
    | D1 d0 -> revapp d0 (D1 d')
    | D2 d0 -> revapp d0 (D2 d')
    | D3 d0 -> revapp d0 (D3 d')
    | D4 d0 -> revapp d0 (D4 d')
    | D5 d0 -> revapp d0 (D5 d')
    | D6 d0 -> revapp d0 (D6 d')
    | D7 d0 -> revapp d0 (D7 d')
    | D8 d0 -> revapp d0 (D8 d')
    | D9 d0 -> revapp d0 (D9 d')

  (** val rev : uint -> uint **)

  let rev d =
    revapp d Nil

  module Little =
   struct
    (** val double : uint -> uint **)

    let rec double = function
    | Nil -> Nil
    | D0 d0 -> D0 (double d0)
    | D1 d0 -> D2 (double d0)
    | D2 d0 -> D4 (double d0)
    | D3 d0 -> D6 (double d0)
    | D4 d0 -> D8 (double d0)
    | D5 d0 -> D0 (succ_double d0)
    | D6 d0 -> D2 (succ_double d0)
    | D7 d0 -> D4 (succ_double d0)
    | D8 d0 -> D6 (succ_double d0)
    | D9 d0 -> D8 (succ_double d0)

    (** val succ_double : uint -> uint **)

    and succ_double = function
    | Nil -> D1 Nil
    | D0 d0 -> D1 (double d0)
    | D1 d0 -> D3 (double d0)
    | D2 d0 -> D5 (double d0)
    | D3 d0 -> D7 (double d0)
    | D4 d0 -> D9 (double d0)
    | D5 d0 -> D1 (succ_double d0)
    | D6 d0 -> D3 (succ_double d0)
    | D7 d0 -> D5 (succ_double d0)
    | D8 d0 -> D7 (succ_double d0)
    | D9 d0 -> D9 (succ_double d0)

    module Pos =
     struct
      (** val to_little_uint : positive -> uint **)

      let rec to_little_uint = function
      | XI p0 -> succ_double (to_little_uint p0)
      | XO p0 -> double (to_little_uint p0)
      | XH -> D1 Nil

      (** val to_uint : positive -> uint **)

      let to_uint p =
        rev (to_little_uint p)

      module String =
       struct
        (** val of_uint : uint -> char list **)

        let rec of_uint = function
        | Nil -> []
        | D0 x -> '0'::(of_uint x)
        | D1 x -> '1'::(of_uint x)
        | D2 x -> '2'::(of_uint x)
        | D3 x -> '3'::(of_uint x)
        | D4 x -> '4'::(of_uint x)
        | D5 x -> '5'::(of_uint x)
        | D6 x -> '6'::(of_uint x)
        | D7 x -> '7'::(of_uint x)
        | D8 x -> '8'::(of_uint x)
        | D9 x -> '9'::(of_uint x)

        (** val decimal_string_of_pos : positive -> char list **)

        let decimal_string_of_pos p =
          of_uint (to_uint p)

        (** val decimal_string_of_Z : z -> char list **)

        let decimal_string_of_Z = function
        | Z0 -> '0'::[]
        | Zpos p -> decimal_string_of_pos p
        | Zneg p -> '-'::(decimal_string_of_pos p)

        type 't coq_Show = bool -> 't -> char list

        (** val show : 'a1 coq_Show -> bool -> 'a1 -> char list **)

        let show show0 =
          show0

        (** val maybe_wrap_parens : bool -> char list -> char list **)

        let maybe_wrap_parens parens s =
          if parens then append ('('::[]) (append s (')'::[])) else s

        (** val show_unit : unit coq_Show **)

        let show_unit _ _ =
          't'::('t'::[])

        (** val show_bool : bool coq_Show **)

        let show_bool _ = function
        | true -> 't'::('r'::('u'::('e'::[])))
        | false -> 'f'::('a'::('l'::('s'::('e'::[]))))

        (** val show_positive : positive coq_Show **)

        let show_positive _ =
          decimal_string_of_pos

        (** val show_N : n coq_Show **)

        let show_N _ = function
        | N0 -> '0'::[]
        | Npos p -> show show_positive false p

        (** val show_nat : nat coq_Show **)

        let show_nat _ n0 =
          show show_N false (N.of_nat n0)

        module Hex =
         struct
          (** val show_Z : z coq_Show **)

          let show_Z _ =
            of_Z

          (** val bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option **)

          let bind v f =
            match v with
            | Some v0 -> f v0
            | None -> None

          module ZRange =
           struct
            type zrange = { lower : z; upper : z }

            (** val lower : zrange -> z **)

            let lower x = x.lower

            (** val upper : zrange -> z **)

            let upper x = x.upper

            (** val is_tighter_than_bool : zrange -> zrange -> bool **)

            let is_tighter_than_bool x y =
              (&&) (Z.leb y.lower x.lower) (Z.leb x.upper y.upper)

            (** val show_zrange : zrange coq_Show **)

            let show_zrange _ r =
              append ('['::[])
                (append (show_Z false r.lower)
                  (append (' '::('~'::('>'::(' '::[]))))
                    (append (show_Z false r.upper) (']'::[]))))

            module Language =
             struct
              module Compilers =
               struct
                module Coq_type =
                 struct
                  type 'base_type coq_type =
                  | Coq_base of 'base_type
                  | Coq_arrow of 'base_type coq_type * 'base_type coq_type

                  type ('base_type, 'base_interp) interp = __
                 end

                module Coq_base =
                 struct
                  module Coq_type =
                   struct
                    type base =
                    | Coq_unit
                    | Z
                    | Coq_bool
                    | Coq_nat

                    type coq_type =
                    | Coq_type_base of base
                    | Coq_prod of coq_type * coq_type
                    | Coq_list of coq_type
                   end

                  type interp = __
                 end

                module Coq_expr =
                 struct
                  type ('base_type, 'ident, 'var) expr =
                  | Ident of 'base_type Coq_type.coq_type * 'ident
                  | Var of 'base_type Coq_type.coq_type * 'var
                  | Abs of 'base_type Coq_type.coq_type
                     * 'base_type Coq_type.coq_type
                     * ('var -> ('base_type, 'ident, 'var) expr)
                  | App of 'base_type Coq_type.coq_type
                     * 'base_type Coq_type.coq_type
                     * ('base_type, 'ident, 'var) expr
                     * ('base_type, 'ident, 'var) expr
                  | LetIn of 'base_type Coq_type.coq_type
                     * 'base_type Coq_type.coq_type
                     * ('base_type, 'ident, 'var) expr
                     * ('var -> ('base_type, 'ident, 'var) expr)
                 end

                module Coq_ident =
                 struct
                  type ident =
                  | Literal of Coq_base.Coq_type.base * Coq_base.interp
                  | Nat_succ
                  | Nat_pred
                  | Nat_max
                  | Nat_mul
                  | Nat_add
                  | Nat_sub
                  | Coq_nil of Coq_base.Coq_type.coq_type
                  | Coq_cons of Coq_base.Coq_type.coq_type
                  | Coq_pair of Coq_base.Coq_type.coq_type
                     * Coq_base.Coq_type.coq_type
                  | Coq_fst of Coq_base.Coq_type.coq_type
                     * Coq_base.Coq_type.coq_type
                  | Coq_snd of Coq_base.Coq_type.coq_type
                     * Coq_base.Coq_type.coq_type
                  | Coq_pair_rect of Coq_base.Coq_type.coq_type
                     * Coq_base.Coq_type.coq_type * Coq_base.Coq_type.coq_type
                  | Coq_bool_rect of Coq_base.Coq_type.coq_type
                  | Coq_nat_rect of Coq_base.Coq_type.coq_type
                  | Coq_list_rect of Coq_base.Coq_type.coq_type
                     * Coq_base.Coq_type.coq_type
                  | Coq_list_case of Coq_base.Coq_type.coq_type
                     * Coq_base.Coq_type.coq_type
                  | List_length of Coq_base.Coq_type.coq_type
                  | List_seq
                  | List_repeat of Coq_base.Coq_type.coq_type
                  | List_combine of Coq_base.Coq_type.coq_type
                     * Coq_base.Coq_type.coq_type
                  | List_map of Coq_base.Coq_type.coq_type
                     * Coq_base.Coq_type.coq_type
                  | List_app of Coq_base.Coq_type.coq_type
                  | List_rev of Coq_base.Coq_type.coq_type
                  | List_flat_map of Coq_base.Coq_type.coq_type
                     * Coq_base.Coq_type.coq_type
                  | List_partition of Coq_base.Coq_type.coq_type
                  | List_fold_right of Coq_base.Coq_type.coq_type
                     * Coq_base.Coq_type.coq_type
                  | List_update_nth of Coq_base.Coq_type.coq_type
                  | List_nth_default of Coq_base.Coq_type.coq_type
                  | Z_add
                  | Z_mul
                  | Z_pow
                  | Z_sub
                  | Z_opp
                  | Z_div
                  | Z_modulo
                  | Z_log2
                  | Z_log2_up
                  | Z_eqb
                  | Z_leb
                  | Z_geb
                  | Z_of_nat
                  | Z_to_nat
                  | Z_shiftr
                  | Z_shiftl
                  | Z_land
                  | Z_lor
                  | Z_bneg
                  | Z_lnot_modulo
                  | Z_mul_split
                  | Z_add_get_carry
                  | Z_add_with_carry
                  | Z_add_with_get_carry
                  | Z_sub_get_borrow
                  | Z_sub_with_get_borrow
                  | Z_zselect
                  | Z_add_modulo
                  | Z_rshi
                  | Z_cc_m
                  | Z_cast of zrange
                  | Z_cast2 of (zrange * zrange)
                  | Coq_fancy_add of z * z
                  | Coq_fancy_addc of z * z
                  | Coq_fancy_sub of z * z
                  | Coq_fancy_subb of z * z
                  | Coq_fancy_mulll of z
                  | Coq_fancy_mullh of z
                  | Coq_fancy_mulhl of z
                  | Coq_fancy_mulhh of z
                  | Coq_fancy_rshi of z * z
                  | Coq_fancy_selc
                  | Coq_fancy_selm of z
                  | Coq_fancy_sell
                  | Coq_fancy_addm
                 end
                module Coq__1 = Coq_ident

                module Coq_invert_expr =
                 struct
                  module Coq_ident =
                   struct
                    (** val invert_Literal :
                        Coq_base.Coq_type.coq_type Coq_type.coq_type ->
                        Coq_ident.ident -> (Coq_base.Coq_type.coq_type,
                        Coq_base.interp) Coq_type.interp option **)

                    let invert_Literal _ = function
                    | Coq_ident.Literal (_, n0) -> Some n0
                    | Coq_ident.Nat_succ -> None
                    | Coq_ident.Nat_pred -> None
                    | Coq_ident.Nat_max -> None
                    | Coq_ident.Nat_mul -> None
                    | Coq_ident.Nat_add -> None
                    | Coq_ident.Nat_sub -> None
                    | Coq_ident.Coq_nil _ -> None
                    | Coq_ident.Coq_cons _ -> None
                    | Coq_ident.Coq_pair (_, _) -> None
                    | Coq_ident.Coq_fst (_, _) -> None
                    | Coq_ident.Coq_snd (_, _) -> None
                    | Coq_ident.Coq_pair_rect (_, _, _) -> None
                    | Coq_ident.Coq_bool_rect _ -> None
                    | Coq_ident.Coq_nat_rect _ -> None
                    | Coq_ident.Coq_list_rect (_, _) -> None
                    | Coq_ident.Coq_list_case (_, _) -> None
                    | Coq_ident.List_length _ -> None
                    | Coq_ident.List_seq -> None
                    | Coq_ident.List_repeat _ -> None
                    | Coq_ident.List_combine (_, _) -> None
                    | Coq_ident.List_map (_, _) -> None
                    | Coq_ident.List_app _ -> None
                    | Coq_ident.List_rev _ -> None
                    | Coq_ident.List_flat_map (_, _) -> None
                    | Coq_ident.List_partition _ -> None
                    | Coq_ident.List_fold_right (_, _) -> None
                    | Coq_ident.List_update_nth _ -> None
                    | Coq_ident.List_nth_default _ -> None
                    | Coq_ident.Z_add -> None
                    | Coq_ident.Z_mul -> None
                    | Coq_ident.Z_pow -> None
                    | Coq_ident.Z_sub -> None
                    | Coq_ident.Z_opp -> None
                    | Coq_ident.Z_div -> None
                    | Coq_ident.Z_modulo -> None
                    | Coq_ident.Z_log2 -> None
                    | Coq_ident.Z_log2_up -> None
                    | Coq_ident.Z_eqb -> None
                    | Coq_ident.Z_leb -> None
                    | Coq_ident.Z_geb -> None
                    | Coq_ident.Z_of_nat -> None
                    | Coq_ident.Z_to_nat -> None
                    | Coq_ident.Z_shiftr -> None
                    | Coq_ident.Z_shiftl -> None
                    | Coq_ident.Z_land -> None
                    | Coq_ident.Z_lor -> None
                    | Coq_ident.Z_bneg -> None
                    | Coq_ident.Z_lnot_modulo -> None
                    | Coq_ident.Z_mul_split -> None
                    | Coq_ident.Z_add_get_carry -> None
                    | Coq_ident.Z_add_with_carry -> None
                    | Coq_ident.Z_add_with_get_carry -> None
                    | Coq_ident.Z_sub_get_borrow -> None
                    | Coq_ident.Z_sub_with_get_borrow -> None
                    | Coq_ident.Z_zselect -> None
                    | Coq_ident.Z_add_modulo -> None
                    | Coq_ident.Z_rshi -> None
                    | Coq_ident.Z_cc_m -> None
                    | Coq_ident.Z_cast _ -> None
                    | Coq_ident.Z_cast2 _ -> None
                    | Coq_ident.Coq_fancy_add (_, _) -> None
                    | Coq_ident.Coq_fancy_addc (_, _) -> None
                    | Coq_ident.Coq_fancy_sub (_, _) -> None
                    | Coq_ident.Coq_fancy_subb (_, _) -> None
                    | Coq_ident.Coq_fancy_mulll _ -> None
                    | Coq_ident.Coq_fancy_mullh _ -> None
                    | Coq_ident.Coq_fancy_mulhl _ -> None
                    | Coq_ident.Coq_fancy_mulhh _ -> None
                    | Coq_ident.Coq_fancy_rshi (_, _) -> None
                    | Coq_ident.Coq_fancy_selc -> None
                    | Coq_ident.Coq_fancy_selm _ -> None
                    | Coq_ident.Coq_fancy_sell -> None
                    | Coq_ident.Coq_fancy_addm -> None
                   end

                  (** val invert_Literal :
                      Coq_base.Coq_type.coq_type Coq_type.coq_type ->
                      (Coq_base.Coq_type.coq_type, Coq__1.ident, 'a1)
                      Coq_expr.expr -> (Coq_base.Coq_type.coq_type,
                      Coq_base.interp) Coq_type.interp option **)

                  let invert_Literal _ = function
                  | Coq_expr.Ident (t, idc) -> Coq_ident.invert_Literal t idc
                  | Coq_expr.Var (_, _) -> None
                  | Coq_expr.Abs (_, _, _) -> None
                  | Coq_expr.App (_, _, _, _) -> None
                  | Coq_expr.LetIn (_, _, _, _) -> None
                 end

                module Coq_defaults =
                 struct
                  (** val type_base :
                      Coq_base.Coq_type.coq_type ->
                      Coq_base.Coq_type.coq_type Coq_type.coq_type **)

                  let type_base t =
                    Coq_type.Coq_base t
                 end
               end
             end

            module Compilers =
             struct
              module ToString =
               struct
                module PHOAS =
                 struct
                  module Coq_type =
                   struct
                    module Coq_base =
                     struct
                      (** val show_base :
                          Language.Compilers.Coq_base.Coq_type.base coq_Show **)

                      let show_base _ = function
                      | Language.Compilers.Coq_base.Coq_type.Coq_unit ->
                        '('::(')'::[])
                      | Language.Compilers.Coq_base.Coq_type.Z ->
                        '\226'::('\132'::('\164'::[]))
                      | Language.Compilers.Coq_base.Coq_type.Coq_bool ->
                        '\240'::('\157'::('\148'::('\185'::[])))
                      | Language.Compilers.Coq_base.Coq_type.Coq_nat ->
                        '\226'::('\132'::('\149'::[]))

                      (** val show_type :
                          bool ->
                          Language.Compilers.Coq_base.Coq_type.coq_type ->
                          char list **)

                      let rec show_type with_parens = function
                      | Language.Compilers.Coq_base.Coq_type.Coq_type_base t0 ->
                        show show_base with_parens t0
                      | Language.Compilers.Coq_base.Coq_type.Coq_prod (
                          a, b) ->
                        maybe_wrap_parens with_parens
                          (append (show_type false a)
                            (append (' '::('*'::(' '::[])))
                              (show_type true b)))
                      | Language.Compilers.Coq_base.Coq_type.Coq_list a ->
                        append ('['::[])
                          (append (show_type false a) (']'::[]))

                      (** val show :
                          Language.Compilers.Coq_base.Coq_type.coq_type
                          coq_Show **)

                      let show =
                        show_type
                     end

                    (** val show_type :
                        'a1 coq_Show -> bool -> 'a1
                        Language.Compilers.Coq_type.coq_type -> char list **)

                    let rec show_type s with_parens = function
                    | Language.Compilers.Coq_type.Coq_base t0 ->
                      s with_parens t0
                    | Language.Compilers.Coq_type.Coq_arrow (s0, d) ->
                      maybe_wrap_parens with_parens
                        (append (show_type s true s0)
                          (append
                            (' '::('\226'::('\134'::('\146'::(' '::[])))))
                            (show_type s false d)))

                    (** val show :
                        'a1 coq_Show -> 'a1
                        Language.Compilers.Coq_type.coq_type coq_Show **)

                    let show =
                      show_type
                   end

                  module Coq_ident =
                   struct
                    (** val show_range_or_ctype : zrange -> char list **)

                    let show_range_or_ctype v =
                      if (&&) (Z.eqb v.lower Z0)
                           (Z.eqb v.upper
                             (Z.sub
                               (Z.pow (Zpos (XO XH))
                                 (Z.log2 (Z.add v.upper (Zpos XH)))) (Zpos
                               XH)))
                      then append ('u'::('i'::('n'::('t'::[]))))
                             (append
                               (decimal_string_of_Z
                                 (Z.log2 (Z.add v.upper (Zpos XH))))
                               ('_'::('t'::[])))
                      else let lg2 = Z.add (Zpos XH) (Z.log2 (Z.opp v.lower))
                           in
                           if (&&)
                                (Z.eqb v.lower
                                  (Z.opp
                                    (Z.pow (Zpos (XO XH))
                                      (Z.sub lg2 (Zpos XH)))))
                                (Z.eqb v.upper
                                  (Z.sub
                                    (Z.pow (Zpos (XO XH))
                                      (Z.sub lg2 (Zpos XH))) (Zpos XH)))
                           then append ('i'::('n'::('t'::[])))
                                  (append (decimal_string_of_Z lg2)
                                    ('_'::('t'::[])))
                           else show show_zrange false v

                    (** val show_compact_Z : bool -> z -> char list **)

                    let show_compact_Z with_parens v =
                      let is_neg = Z.ltb v Z0 in
                      append (if is_neg then '-'::[] else [])
                        (let v0 = Z.abs v in
                         if Z.leb v0
                              (Z.pow (Zpos (XO XH)) (Zpos (XO (XO (XO XH)))))
                         then decimal_string_of_Z v0
                         else if Z.eqb v0 (Z.pow (Zpos (XO XH)) (Z.log2 v0))
                              then append ('2'::('^'::[]))
                                     (decimal_string_of_Z (Z.log2 v0))
                              else if Z.eqb v0
                                        (Z.sub
                                          (Z.pow (Zpos (XO XH))
                                            (Z.log2_up v0)) (Zpos XH))
                                   then maybe_wrap_parens is_neg
                                          (append ('2'::('^'::[]))
                                            (append
                                              (decimal_string_of_Z
                                                (Z.log2_up v0))
                                              ('-'::('1'::[]))))
                                   else show_Z with_parens v0)

                    (** val show_ident :
                        Language.Compilers.Coq_base.Coq_type.coq_type
                        Language.Compilers.Coq_type.coq_type ->
                        Language.Compilers.Coq_ident.ident coq_Show **)

                    let show_ident _ with_parens = function
                    | Language.Compilers.Coq_ident.Literal (t, v) ->
                      (match t with
                       | Language.Compilers.Coq_base.Coq_type.Coq_unit ->
                         (fun v0 -> show (Obj.magic show_unit) with_parens v0)
                       | Language.Compilers.Coq_base.Coq_type.Z ->
                         (fun v0 -> show_compact_Z with_parens (Obj.magic v0))
                       | Language.Compilers.Coq_base.Coq_type.Coq_bool ->
                         (fun v0 -> show (Obj.magic show_bool) with_parens v0)
                       | Language.Compilers.Coq_base.Coq_type.Coq_nat ->
                         (fun v0 -> show (Obj.magic show_nat) with_parens v0))
                        v
                    | Language.Compilers.Coq_ident.Nat_succ ->
                      'N'::('a'::('t'::('.'::('s'::('u'::('c'::('c'::[])))))))
                    | Language.Compilers.Coq_ident.Nat_pred ->
                      'N'::('a'::('t'::('.'::('p'::('r'::('e'::('d'::[])))))))
                    | Language.Compilers.Coq_ident.Nat_max ->
                      'N'::('a'::('t'::('.'::('m'::('a'::('x'::[]))))))
                    | Language.Compilers.Coq_ident.Nat_mul ->
                      'N'::('a'::('t'::('.'::('m'::('u'::('l'::[]))))))
                    | Language.Compilers.Coq_ident.Nat_add ->
                      'N'::('a'::('t'::('.'::('a'::('d'::('d'::[]))))))
                    | Language.Compilers.Coq_ident.Nat_sub ->
                      'N'::('a'::('t'::('.'::('s'::('u'::('b'::[]))))))
                    | Language.Compilers.Coq_ident.Coq_nil _ -> '['::(']'::[])
                    | Language.Compilers.Coq_ident.Coq_cons _ ->
                      '('::(':'::(':'::(')'::[])))
                    | Language.Compilers.Coq_ident.Coq_pair (_, _) ->
                      '('::(','::(')'::[]))
                    | Language.Compilers.Coq_ident.Coq_fst (_, _) ->
                      'f'::('s'::('t'::[]))
                    | Language.Compilers.Coq_ident.Coq_snd (_, _) ->
                      's'::('n'::('d'::[]))
                    | Language.Compilers.Coq_ident.Coq_pair_rect (_, _, _) ->
                      'p'::('a'::('i'::('r'::('_'::('r'::('e'::('c'::('t'::[]))))))))
                    | Language.Compilers.Coq_ident.Coq_bool_rect _ ->
                      'b'::('o'::('o'::('l'::('_'::('r'::('e'::('c'::('t'::[]))))))))
                    | Language.Compilers.Coq_ident.Coq_nat_rect _ ->
                      'n'::('a'::('t'::('_'::('r'::('e'::('c'::('t'::[])))))))
                    | Language.Compilers.Coq_ident.Coq_list_rect (_, _) ->
                      'l'::('i'::('s'::('t'::('_'::('r'::('e'::('c'::('t'::[]))))))))
                    | Language.Compilers.Coq_ident.Coq_list_case (_, _) ->
                      'l'::('i'::('s'::('t'::('_'::('c'::('a'::('s'::('e'::[]))))))))
                    | Language.Compilers.Coq_ident.List_length _ ->
                      'l'::('e'::('n'::('g'::('t'::('h'::[])))))
                    | Language.Compilers.Coq_ident.List_seq ->
                      's'::('e'::('q'::[]))
                    | Language.Compilers.Coq_ident.List_repeat _ ->
                      'r'::('e'::('p'::('e'::('a'::('t'::[])))))
                    | Language.Compilers.Coq_ident.List_combine (_, _) ->
                      'c'::('o'::('m'::('b'::('i'::('n'::('e'::[]))))))
                    | Language.Compilers.Coq_ident.List_map (_, _) ->
                      'm'::('a'::('p'::[]))
                    | Language.Compilers.Coq_ident.List_app _ ->
                      '('::('+'::('+'::(')'::[])))
                    | Language.Compilers.Coq_ident.List_rev _ ->
                      'r'::('e'::('v'::[]))
                    | Language.Compilers.Coq_ident.List_flat_map (_, _) ->
                      'f'::('l'::('a'::('t'::('_'::('m'::('a'::('p'::[])))))))
                    | Language.Compilers.Coq_ident.List_partition _ ->
                      'p'::('a'::('r'::('t'::('i'::('t'::('i'::('o'::('n'::[]))))))))
                    | Language.Compilers.Coq_ident.List_fold_right (_, _) ->
                      'f'::('o'::('l'::('d'::('_'::('r'::('i'::('g'::('h'::('t'::[])))))))))
                    | Language.Compilers.Coq_ident.List_update_nth _ ->
                      'u'::('p'::('d'::('a'::('t'::('e'::('_'::('n'::('t'::('h'::[])))))))))
                    | Language.Compilers.Coq_ident.List_nth_default _ ->
                      'n'::('t'::('h'::[]))
                    | Language.Compilers.Coq_ident.Z_add ->
                      '('::('+'::(')'::[]))
                    | Language.Compilers.Coq_ident.Z_mul ->
                      '('::(' '::('*'::(' '::(')'::[]))))
                    | Language.Compilers.Coq_ident.Z_pow ->
                      '('::('^'::(')'::[]))
                    | Language.Compilers.Coq_ident.Z_sub ->
                      '('::('-'::(')'::[]))
                    | Language.Compilers.Coq_ident.Z_opp -> '-'::[]
                    | Language.Compilers.Coq_ident.Z_div ->
                      '('::('/'::(')'::[]))
                    | Language.Compilers.Coq_ident.Z_modulo ->
                      '('::('m'::('o'::('d'::(')'::[]))))
                    | Language.Compilers.Coq_ident.Z_log2 ->
                      'l'::('o'::('g'::('\226'::('\130'::('\130'::[])))))
                    | Language.Compilers.Coq_ident.Z_log2_up ->
                      '\226'::('\140'::('\136'::('l'::('o'::('g'::('\226'::('\130'::('\130'::('\226'::('\140'::('\137'::[])))))))))))
                    | Language.Compilers.Coq_ident.Z_eqb ->
                      '('::('='::(')'::[]))
                    | Language.Compilers.Coq_ident.Z_leb ->
                      '('::('\226'::('\137'::('\164'::(')'::[]))))
                    | Language.Compilers.Coq_ident.Z_geb ->
                      '('::('\226'::('\137'::('\165'::(')'::[]))))
                    | Language.Compilers.Coq_ident.Z_of_nat ->
                      '('::('\226'::('\132'::('\149'::('\226'::('\134'::('\146'::('\226'::('\132'::('\164'::(')'::[]))))))))))
                    | Language.Compilers.Coq_ident.Z_to_nat ->
                      '('::('\226'::('\132'::('\164'::('\226'::('\134'::('\146'::('\226'::('\132'::('\149'::(')'::[]))))))))))
                    | Language.Compilers.Coq_ident.Z_shiftr ->
                      '('::('>'::('>'::(')'::[])))
                    | Language.Compilers.Coq_ident.Z_shiftl ->
                      '('::('<'::('<'::(')'::[])))
                    | Language.Compilers.Coq_ident.Z_land ->
                      '('::('&'::(')'::[]))
                    | Language.Compilers.Coq_ident.Z_lor ->
                      '('::('|'::(')'::[]))
                    | Language.Compilers.Coq_ident.Z_bneg -> '!'::[]
                    | Language.Compilers.Coq_ident.Z_lnot_modulo -> '~'::[]
                    | Language.Compilers.Coq_ident.Z_mul_split ->
                      'Z'::('.'::('m'::('u'::('l'::('_'::('s'::('p'::('l'::('i'::('t'::[]))))))))))
                    | Language.Compilers.Coq_ident.Z_add_get_carry ->
                      'Z'::('.'::('a'::('d'::('d'::('_'::('g'::('e'::('t'::('_'::('c'::('a'::('r'::('r'::('y'::[]))))))))))))))
                    | Language.Compilers.Coq_ident.Z_add_with_carry ->
                      'Z'::('.'::('a'::('d'::('d'::('_'::('w'::('i'::('t'::('h'::('_'::('c'::('a'::('r'::('r'::('y'::[])))))))))))))))
                    | Language.Compilers.Coq_ident.Z_add_with_get_carry ->
                      'Z'::('.'::('a'::('d'::('d'::('_'::('w'::('i'::('t'::('h'::('_'::('g'::('e'::('t'::('_'::('c'::('a'::('r'::('r'::('y'::[])))))))))))))))))))
                    | Language.Compilers.Coq_ident.Z_sub_get_borrow ->
                      'Z'::('.'::('s'::('u'::('b'::('_'::('g'::('e'::('t'::('_'::('b'::('o'::('r'::('r'::('o'::('w'::[])))))))))))))))
                    | Language.Compilers.Coq_ident.Z_sub_with_get_borrow ->
                      'Z'::('.'::('s'::('u'::('b'::('_'::('w'::('i'::('t'::('h'::('_'::('g'::('e'::('t'::('_'::('b'::('o'::('r'::('r'::('o'::('w'::[]))))))))))))))))))))
                    | Language.Compilers.Coq_ident.Z_zselect ->
                      'Z'::('.'::('z'::('s'::('e'::('l'::('e'::('c'::('t'::[]))))))))
                    | Language.Compilers.Coq_ident.Z_add_modulo ->
                      'Z'::('.'::('a'::('d'::('d'::('_'::('m'::('o'::('d'::('u'::('l'::('o'::[])))))))))))
                    | Language.Compilers.Coq_ident.Z_rshi ->
                      'Z'::('.'::('r'::('s'::('h'::('i'::[])))))
                    | Language.Compilers.Coq_ident.Z_cc_m ->
                      'Z'::('.'::('c'::('c'::('_'::('m'::[])))))
                    | Language.Compilers.Coq_ident.Z_cast range ->
                      append ('('::[])
                        (append (show_range_or_ctype range) (')'::[]))
                    | Language.Compilers.Coq_ident.Z_cast2 range ->
                      let (r1, r2) = range in
                      append ('('::[])
                        (append (show_range_or_ctype r1)
                          (append (','::(' '::[]))
                            (append (show_range_or_ctype r2) (')'::[]))))
                    | Language.Compilers.Coq_ident.Coq_fancy_add (log2wordmax,
                                                                  imm) ->
                      maybe_wrap_parens with_parens
                        (append
                          ('f'::('a'::('n'::('c'::('y'::('.'::('a'::('d'::('d'::(' '::('2'::('^'::[]))))))))))))
                          (append (decimal_string_of_Z log2wordmax)
                            (append (' '::[]) (of_Z imm))))
                    | Language.Compilers.Coq_ident.Coq_fancy_addc (log2wordmax,
                                                                   imm) ->
                      maybe_wrap_parens with_parens
                        (append
                          ('f'::('a'::('n'::('c'::('y'::('.'::('a'::('d'::('d'::('c'::(' '::('2'::('^'::[])))))))))))))
                          (append (decimal_string_of_Z log2wordmax)
                            (append (' '::[]) (of_Z imm))))
                    | Language.Compilers.Coq_ident.Coq_fancy_sub (log2wordmax,
                                                                  imm) ->
                      maybe_wrap_parens with_parens
                        (append
                          ('f'::('a'::('n'::('c'::('y'::('.'::('s'::('u'::('b'::(' '::('2'::('^'::[]))))))))))))
                          (append (decimal_string_of_Z log2wordmax)
                            (append (' '::[]) (of_Z imm))))
                    | Language.Compilers.Coq_ident.Coq_fancy_subb (log2wordmax,
                                                                   imm) ->
                      maybe_wrap_parens with_parens
                        (append
                          ('f'::('a'::('n'::('c'::('y'::('.'::('s'::('u'::('b'::('b'::(' '::('2'::('^'::[])))))))))))))
                          (append (decimal_string_of_Z log2wordmax)
                            (append (' '::[]) (of_Z imm))))
                    | Language.Compilers.Coq_ident.Coq_fancy_mulll log2wordmax ->
                      maybe_wrap_parens with_parens
                        (append
                          ('f'::('a'::('n'::('c'::('y'::('.'::('m'::('u'::('l'::('l'::('l'::(' '::('2'::('^'::[]))))))))))))))
                          (decimal_string_of_Z log2wordmax))
                    | Language.Compilers.Coq_ident.Coq_fancy_mullh log2wordmax ->
                      maybe_wrap_parens with_parens
                        (append
                          ('f'::('a'::('n'::('c'::('y'::('.'::('m'::('u'::('l'::('l'::('h'::(' '::('2'::('^'::[]))))))))))))))
                          (decimal_string_of_Z log2wordmax))
                    | Language.Compilers.Coq_ident.Coq_fancy_mulhl log2wordmax ->
                      maybe_wrap_parens with_parens
                        (append
                          ('f'::('a'::('n'::('c'::('y'::('.'::('m'::('u'::('l'::('h'::('l'::(' '::('2'::('^'::[]))))))))))))))
                          (decimal_string_of_Z log2wordmax))
                    | Language.Compilers.Coq_ident.Coq_fancy_mulhh log2wordmax ->
                      maybe_wrap_parens with_parens
                        (append
                          ('f'::('a'::('n'::('c'::('y'::('.'::('m'::('u'::('l'::('h'::('h'::(' '::('2'::('^'::[]))))))))))))))
                          (decimal_string_of_Z log2wordmax))
                    | Language.Compilers.Coq_ident.Coq_fancy_rshi (log2wordmax,
                                                                   x) ->
                      maybe_wrap_parens with_parens
                        (append
                          ('f'::('a'::('n'::('c'::('y'::('.'::('r'::('s'::('h'::('i'::(' '::('2'::('^'::[])))))))))))))
                          (append (decimal_string_of_Z log2wordmax)
                            (append (' '::[]) (decimal_string_of_Z x))))
                    | Language.Compilers.Coq_ident.Coq_fancy_selc ->
                      'f'::('a'::('n'::('c'::('y'::('.'::('s'::('e'::('l'::('c'::[])))))))))
                    | Language.Compilers.Coq_ident.Coq_fancy_selm log2wordmax ->
                      maybe_wrap_parens with_parens
                        (append
                          ('f'::('a'::('n'::('c'::('y'::('.'::('s'::('e'::('l'::('m'::(' '::('2'::('^'::[])))))))))))))
                          (decimal_string_of_Z log2wordmax))
                    | Language.Compilers.Coq_ident.Coq_fancy_sell ->
                      'f'::('a'::('n'::('c'::('y'::('.'::('s'::('e'::('l'::('l'::[])))))))))
                    | Language.Compilers.Coq_ident.Coq_fancy_addm ->
                      'f'::('a'::('n'::('c'::('y'::('.'::('a'::('d'::('d'::('m'::[])))))))))
                   end

                  module Coq_expr =
                   struct
                    (** val show_var_expr :
                        'a1 coq_Show -> ('a1
                        Language.Compilers.Coq_type.coq_type -> 'a2 coq_Show)
                        -> 'a1 Language.Compilers.Coq_type.coq_type -> bool
                        -> ('a1, 'a2, 'a3) Language.Compilers.Coq_expr.expr
                        -> char list **)

                    let show_var_expr show_base_type show_ident0 t with_parens e =
                      let rec show_var_expr0 _ t0 with_parens0 = function
                      | Language.Compilers.Coq_expr.Ident (t1, idc) ->
                        show (show_ident0 t1) with_parens0 idc
                      | Language.Compilers.Coq_expr.Var (t1, _) ->
                        maybe_wrap_parens with_parens0
                          (append ('V'::('A'::('R'::('_'::('('::[])))))
                            (append
                              (show (Coq_type.show show_base_type) false t1)
                              (')'::[])))
                      | Language.Compilers.Coq_expr.Abs (_, _, _) ->
                        append ('\206'::('\187'::('_'::('('::[]))))
                          (append
                            (show (Coq_type.show show_base_type) false t0)
                            (')'::[]))
                      | Language.Compilers.Coq_expr.App (s, d, f, x) ->
                        let show_f =
                          show_var_expr0 __
                            (Language.Compilers.Coq_type.Coq_arrow (s, d))
                            false f
                        in
                        let show_x = show_var_expr0 __ s true x in
                        maybe_wrap_parens with_parens0
                          (append show_f
                            (append (' '::('@'::(' '::[]))) show_x))
                      | Language.Compilers.Coq_expr.LetIn (a, _, x, _) ->
                        let show_x = show_var_expr0 __ a false x in
                        maybe_wrap_parens with_parens0
                          (append
                            ('e'::('x'::('p'::('r'::('_'::('l'::('e'::('t'::(' '::('_'::(' '::(':'::('='::(' '::[]))))))))))))))
                            (append show_x
                              (' '::('i'::('n'::(' '::('_'::[])))))))
                      in show_var_expr0 __ t with_parens e

                    (** val partially_show_expr :
                        'a1 coq_Show -> ('a1
                        Language.Compilers.Coq_type.coq_type -> 'a2 coq_Show)
                        -> 'a1 Language.Compilers.Coq_type.coq_type -> ('a1,
                        'a2, 'a3) Language.Compilers.Coq_expr.expr coq_Show **)

                    let partially_show_expr =
                      show_var_expr
                   end
                 end

                module C =
                 struct
                  module Coq_type =
                   struct
                    type primitive =
                    | Z
                    | Zptr

                    type coq_type =
                    | Coq_type_primitive of primitive
                    | Coq_prod of coq_type * coq_type
                    | Coq_unit
                   end

                  module Coq_int =
                   struct
                    type coq_type =
                    | Coq_signed of nat
                    | Coq_unsigned of nat

                    (** val lgbitwidth_of : coq_type -> nat **)

                    let lgbitwidth_of = function
                    | Coq_signed lgbitwidth -> lgbitwidth
                    | Coq_unsigned lgbitwidth -> lgbitwidth

                    (** val bitwidth_of : coq_type -> z **)

                    let bitwidth_of t =
                      Z.pow (Zpos (XO XH)) (Z.of_nat (lgbitwidth_of t))

                    (** val is_signed : coq_type -> bool **)

                    let is_signed = function
                    | Coq_signed _ -> true
                    | Coq_unsigned _ -> false

                    (** val is_unsigned : coq_type -> bool **)

                    let is_unsigned t =
                      negb (is_signed t)

                    (** val to_zrange : coq_type -> zrange **)

                    let to_zrange t =
                      let bw = bitwidth_of t in
                      if is_signed t
                      then { lower = (Z.opp (Z.pow (Zpos (XO XH)) bw));
                             upper =
                             (Z.sub
                               (Z.pow (Zpos (XO XH)) (Z.sub bw (Zpos XH)))
                               (Zpos XH)) }
                      else { lower = Z0; upper =
                             (Z.sub (Z.pow (Zpos (XO XH)) bw) (Zpos XH)) }

                    (** val show_type : coq_type coq_Show **)

                    let show_type with_parens t =
                      maybe_wrap_parens with_parens
                        (append (if is_unsigned t then 'u'::[] else [])
                          (append ('i'::('n'::('t'::[])))
                            (decimal_string_of_Z (bitwidth_of t))))
                   end

                  type ident =
                  | Coq_literal of z
                  | List_nth of nat
                  | Addr
                  | Dereference
                  | Z_shiftr of z
                  | Z_shiftl of z
                  | Z_land
                  | Z_lor
                  | Z_add
                  | Z_mul
                  | Z_sub
                  | Z_opp
                  | Z_lnot of Coq_int.coq_type
                  | Z_bneg
                  | Z_mul_split of z
                  | Z_add_with_get_carry of z
                  | Z_sub_with_get_borrow of z
                  | Z_zselect of Coq_int.coq_type
                  | Z_add_modulo
                  | Z_static_cast of Coq_int.coq_type

                  type arith_expr =
                  | AppIdent of Coq_type.coq_type * Coq_type.coq_type * 
                     ident * arith_expr
                  | Var of Coq_type.primitive * char list
                  | Pair of Coq_type.coq_type * Coq_type.coq_type
                     * arith_expr * arith_expr
                  | TT

                  type stmt =
                  | Call of arith_expr
                  | Assign of bool * Coq_type.primitive
                     * Coq_int.coq_type option * char list * arith_expr
                  | AssignZPtr of char list * Coq_int.coq_type option
                     * arith_expr
                  | DeclareVar of Coq_type.primitive
                     * Coq_int.coq_type option * char list
                  | AssignNth of char list * nat * arith_expr

                  type expr = stmt list

                  module OfPHOAS =
                   struct
                    type var_data = __

                    (** val bind2_err :
                        ('a1, char list list) sum -> ('a2, char list list)
                        sum -> ('a1 -> 'a2 -> ('a3, char list list) sum) ->
                        ('a3, char list list) sum **)

                    let bind2_err v1 v2 f =
                      match v1 with
                      | Inl x1 ->
                        (match v2 with
                         | Inl x2 -> f x1 x2
                         | Inr err -> Inr err)
                      | Inr err1 ->
                        (match v2 with
                         | Inl _ -> Inr err1
                         | Inr err2 -> Inr (app err1 err2))

                    (** val bind4_err :
                        ('a1, char list list) sum -> ('a2, char list list)
                        sum -> ('a3, char list list) sum -> ('a4, char list
                        list) sum -> ('a1 -> 'a2 -> 'a3 -> 'a4 -> ('a5,
                        char list list) sum) -> ('a5, char list list) sum **)

                    let bind4_err v1 v2 v3 v4 f =
                      bind2_err (bind2_err v1 v2 (fun x1 x2 -> Inl (x1, x2)))
                        (bind2_err v3 v4 (fun x3 x4 -> Inl (x3, x4)))
                        (fun x12 x34 ->
                        let (p, p0) = (x12, x34) in
                        let (x1, x2) = p in let (x3, x4) = p0 in f x1 x2 x3 x4)

                    (** val maybe_log2 : z -> z option **)

                    let maybe_log2 s =
                      if Z.eqb (Z.pow (Zpos (XO XH)) (Z.log2 s)) s
                      then Some (Z.log2 s)
                      else None

                    (** val bounds_check :
                        char list ->
                        Language.Compilers.Coq_base.Coq_type.coq_type
                        Language.Compilers.Coq_type.coq_type ->
                        Language.Compilers.Coq_ident.ident -> z ->
                        Language.Compilers.Coq_base.Coq_type.coq_type
                        Language.Compilers.Coq_type.coq_type ->
                        (Language.Compilers.Coq_base.Coq_type.coq_type,
                        Language.Compilers.Coq_ident.ident, var_data)
                        Language.Compilers.Coq_expr.expr -> Coq_int.coq_type
                        option -> (unit, char list list) sum **)

                    let bounds_check descr t idc s t' ev found =
                      let x = fun _ _ x x0 _ ->
                        PHOAS.Coq_expr.partially_show_expr x x0
                      in
                      (match found with
                       | Some ty ->
                         if is_tighter_than_bool (Coq_int.to_zrange ty)
                              { lower = Z0; upper =
                              (Z.sub (Z.pow (Zpos (XO XH)) s) (Zpos XH)) }
                         then Inl ()
                         else Inr
                                ((append
                                   ('F'::('i'::('n'::('a'::('l'::(' '::('b'::('o'::('u'::('n'::('d'::('s'::(' '::('c'::('h'::('e'::('c'::('k'::(' '::('f'::('a'::('i'::('l'::('e'::('d'::(' '::('o'::('n'::(' '::[])))))))))))))))))))))))))))))
                                   (append descr
                                     (append (' '::[])
                                       (append
                                         (show (PHOAS.Coq_ident.show_ident t)
                                           false idc)
                                         (append
                                           (';'::(' '::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::('a'::('n'::(' '::('u'::('n'::('s'::('i'::('g'::('n'::('e'::('d'::(' '::[])))))))))))))))))))))))
                                           (append (decimal_string_of_Z s)
                                             (append
                                               ('-'::('b'::('i'::('t'::(' '::('n'::('u'::('m'::('b'::('e'::('r'::(','::(' '::('b'::('u'::('t'::(' '::('f'::('o'::('u'::('n'::('d'::(' '::('a'::(' '::[])))))))))))))))))))))))))
                                               (append
                                                 (show Coq_int.show_type
                                                   false ty) ('.'::[]))))))))) :: [])
                       | None ->
                         Inr
                           ((append
                              ('M'::('i'::('s'::('s'::('i'::('n'::('g'::(' '::('r'::('a'::('n'::('g'::('e'::(' '::('o'::('n'::(' '::[])))))))))))))))))
                              (append descr
                                (append (' '::[])
                                  (append
                                    (show (PHOAS.Coq_ident.show_ident t) true
                                      idc)
                                    (append (':'::(' '::[]))
                                      (show
                                        (x __ __ PHOAS.Coq_type.Coq_base.show
                                          PHOAS.Coq_ident.show_ident __ t')
                                        true ev)))))) :: []))

                    (** val admit : 'a1 **)

                    let admit =
                      failwith "AXIOM TO BE REALIZED"

                    (** val recognize_3arg_2ref_ident :
                        Language.Compilers.Coq_ident.ident ->
                        (Coq_int.coq_type option * Coq_int.coq_type option)
                        -> (((Language.Compilers.Coq_base.Coq_type.coq_type,
                        Language.Compilers.Coq_ident.ident, var_data)
                        Language.Compilers.Coq_expr.expr * (arith_expr * Coq_int.coq_type
                        option)) * (((Language.Compilers.Coq_base.Coq_type.coq_type,
                        Language.Compilers.Coq_ident.ident, var_data)
                        Language.Compilers.Coq_expr.expr * (arith_expr * Coq_int.coq_type
                        option)) * (((Language.Compilers.Coq_base.Coq_type.coq_type,
                        Language.Compilers.Coq_ident.ident, var_data)
                        Language.Compilers.Coq_expr.expr * (arith_expr * Coq_int.coq_type
                        option)) * __))) -> (arith_expr -> expr, char list
                        list) sum **)

                    let recognize_3arg_2ref_ident =
                      let t = Language.Compilers.Coq_type.Coq_arrow
                        ((Language.Compilers.Coq_defaults.type_base
                           (Language.Compilers.Coq_base.Coq_type.Coq_type_base
                           Language.Compilers.Coq_base.Coq_type.Z)),
                        (Language.Compilers.Coq_type.Coq_arrow
                        ((Language.Compilers.Coq_defaults.type_base
                           (Language.Compilers.Coq_base.Coq_type.Coq_type_base
                           Language.Compilers.Coq_base.Coq_type.Z)),
                        (Language.Compilers.Coq_type.Coq_arrow
                        ((Language.Compilers.Coq_defaults.type_base
                           (Language.Compilers.Coq_base.Coq_type.Coq_type_base
                           Language.Compilers.Coq_base.Coq_type.Z)),
                        (Language.Compilers.Coq_defaults.type_base
                          (Language.Compilers.Coq_base.Coq_type.Coq_prod
                          ((Language.Compilers.Coq_base.Coq_type.Coq_type_base
                          Language.Compilers.Coq_base.Coq_type.Z),
                          (Language.Compilers.Coq_base.Coq_type.Coq_type_base
                          Language.Compilers.Coq_base.Coq_type.Z)))))))))
                      in
                      (fun idc rout args ->
                      let (p, f) = args in
                      let (s, _) = p in
                      let (p0, p1) = f in
                      let (e1v, p2) = p0 in
                      let (e1, r1) = p2 in
                      let (p3, f0) = p1 in
                      let (e2v, p4) = p3 in
                      let (e2, r2) = p4 in
                      let () = Obj.magic f0 in
                      (match bind
                               (Obj.magic
                                 Language.Compilers.Coq_invert_expr.invert_Literal
                                 (Language.Compilers.Coq_defaults.type_base
                                   (Language.Compilers.Coq_base.Coq_type.Coq_type_base
                                   Language.Compilers.Coq_base.Coq_type.Z)) s)
                               maybe_log2 with
                       | Some s0 ->
                         bind4_err
                           (bounds_check [] t idc s0
                             (Language.Compilers.Coq_defaults.type_base
                               (Language.Compilers.Coq_base.Coq_type.Coq_type_base
                               Language.Compilers.Coq_base.Coq_type.Z)) e1v
                             r1)
                           (bounds_check [] t idc s0
                             (Language.Compilers.Coq_defaults.type_base
                               (Language.Compilers.Coq_base.Coq_type.Coq_type_base
                               Language.Compilers.Coq_base.Coq_type.Z)) e2v
                             r2)
                           (bounds_check [] t idc s0
                             (Language.Compilers.Coq_defaults.type_base
                               (Language.Compilers.Coq_base.Coq_type.Coq_type_base
                               Language.Compilers.Coq_base.Coq_type.Z)) e2v
                             (fst rout))
                           (bounds_check [] t idc s0
                             (Language.Compilers.Coq_defaults.type_base
                               (Language.Compilers.Coq_base.Coq_type.Coq_type_base
                               Language.Compilers.Coq_base.Coq_type.Z)) e2v
                             (snd rout)) (fun _ _ _ _ -> Inl (fun retptr ->
                           (Call (AppIdent ((Coq_type.Coq_prod
                           ((Coq_type.Coq_prod ((Coq_type.Coq_type_primitive
                           Coq_type.Zptr), (Coq_type.Coq_type_primitive
                           Coq_type.Zptr))), (Coq_type.Coq_prod
                           ((Coq_type.Coq_type_primitive Coq_type.Z),
                           (Coq_type.Coq_type_primitive Coq_type.Z))))),
                           Coq_type.Coq_unit, (Z_mul_split s0), (Pair
                           ((Coq_type.Coq_prod ((Coq_type.Coq_type_primitive
                           Coq_type.Zptr), (Coq_type.Coq_type_primitive
                           Coq_type.Zptr))), (Coq_type.Coq_prod
                           ((Coq_type.Coq_type_primitive Coq_type.Z),
                           (Coq_type.Coq_type_primitive Coq_type.Z))),
                           retptr, (Pair ((Coq_type.Coq_type_primitive
                           Coq_type.Z), (Coq_type.Coq_type_primitive
                           Coq_type.Z), e1, e2))))))) :: []))
                       | None -> admit))
                   end
                 end
               end
             end
           end
         end
       end
     end
   end
 end

