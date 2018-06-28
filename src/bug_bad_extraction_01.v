(* -*- mode: coq; coq-prog-args: ("-emacs" "-R" "." "Crypto" "-R" "../bbv" "bbv" "-R" "../coqprime/src/Coqprime" "Coqprime" "-top" "bug") -*- *)
(* File reduced by coq-bug-finder from original input, then from 1307 lines to 355 lines, then from 2069 lines to 547 lines, then from 633 lines to 553 lines, then from 729 lines to 560 lines, then from 870 lines to 568 lines, then from 744 lines to 593 lines, then from 867 lines to 693 lines, then from 870 lines to 694 lines, then from 747 lines to 696 lines, then from 949 lines to 743 lines, then from 759 lines to 744 lines *)
(* coqc version 8.8.0 (May 2018) compiled on May 29 2018 14:57:33 with OCaml 4.02.3
   coqtop version 8.8.0 (May 2018) *)
Require Coq.QArith.QArith_base.
Require Coq.Strings.String.

Module Export HexString.
Import Coq.Strings.String.
Import BinPosDef.

Local Open Scope positive_scope.

Module Export Raw.
  Fixpoint of_pos (p : positive) (rest : string) : string
    := match p with
       | 1 => String "1" rest
       | 2 => String "2" rest
       | 3 => String "3" rest
       | 4 => String "4" rest
       | 5 => String "5" rest
       | 6 => String "6" rest
       | 7 => String "7" rest
       | 8 => String "8" rest
       | 9 => String "9" rest
       | 10 => String "a" rest
       | 11 => String "b" rest
       | 12 => String "c" rest
       | 13 => String "d" rest
       | 14 => String "e" rest
       | 15 => String "f" rest
       | p'~0~0~0~0 => of_pos p' (String "0" rest)
       | p'~0~0~0~1 => of_pos p' (String "1" rest)
       | p'~0~0~1~0 => of_pos p' (String "2" rest)
       | p'~0~0~1~1 => of_pos p' (String "3" rest)
       | p'~0~1~0~0 => of_pos p' (String "4" rest)
       | p'~0~1~0~1 => of_pos p' (String "5" rest)
       | p'~0~1~1~0 => of_pos p' (String "6" rest)
       | p'~0~1~1~1 => of_pos p' (String "7" rest)
       | p'~1~0~0~0 => of_pos p' (String "8" rest)
       | p'~1~0~0~1 => of_pos p' (String "9" rest)
       | p'~1~0~1~0 => of_pos p' (String "a" rest)
       | p'~1~0~1~1 => of_pos p' (String "b" rest)
       | p'~1~1~0~0 => of_pos p' (String "c" rest)
       | p'~1~1~0~1 => of_pos p' (String "d" rest)
       | p'~1~1~1~0 => of_pos p' (String "e" rest)
       | p'~1~1~1~1 => of_pos p' (String "f" rest)
       end.
End Raw.

Definition of_pos (p : positive) : string
  := String "0" (String "x" (Raw.of_pos p "")).
Definition of_Z (z : Z) : string
  := match z with
     | Zneg p => String "-" (of_pos p)
     | Z0 => "0x0"
     | Zpos p => of_pos p
     end.

Global Set Asymmetric Patterns.

Reserved Infix "@@" (left associativity, at level 11).
Reserved Notation "A <- X ; B" (at level 70, X at next level, right associativity, format "'[v' A  <-  X ; '/' B ']'").

  Inductive uint :=
  | Nil
  | D0 (_:uint)
  | D1 (_:uint)
  | D2 (_:uint)
  | D3 (_:uint)
  | D4 (_:uint)
  | D5 (_:uint)
  | D6 (_:uint)
  | D7 (_:uint)
  | D8 (_:uint)
  | D9 (_:uint).

  Fixpoint revapp (d d' : uint) :=
    match d with
    | Nil => d'
    | D0 d => revapp d (D0 d')
    | D1 d => revapp d (D1 d')
    | D2 d => revapp d (D2 d')
    | D3 d => revapp d (D3 d')
    | D4 d => revapp d (D4 d')
    | D5 d => revapp d (D5 d')
    | D6 d => revapp d (D6 d')
    | D7 d => revapp d (D7 d')
    | D8 d => revapp d (D8 d')
    | D9 d => revapp d (D9 d')
    end.

  Definition rev d := revapp d Nil.

  Module Export Little.

    Fixpoint double d :=
      match d with
      | Nil => Nil
      | D0 d => D0 (double d)
      | D1 d => D2 (double d)
      | D2 d => D4 (double d)
      | D3 d => D6 (double d)
      | D4 d => D8 (double d)
      | D5 d => D0 (succ_double d)
      | D6 d => D2 (succ_double d)
      | D7 d => D4 (succ_double d)
      | D8 d => D6 (succ_double d)
      | D9 d => D8 (succ_double d)
      end

    with succ_double d :=
           match d with
           | Nil => D1 Nil
           | D0 d => D1 (double d)
           | D1 d => D3 (double d)
           | D2 d => D5 (double d)
           | D3 d => D7 (double d)
           | D4 d => D9 (double d)
           | D5 d => D1 (succ_double d)
           | D6 d => D3 (succ_double d)
           | D7 d => D5 (succ_double d)
           | D8 d => D7 (succ_double d)
           | D9 d => D9 (succ_double d)
           end.

  Module Export Pos.
    Fixpoint to_little_uint p :=
      match p with
      | 1 => D1 Nil
      | p~1 => Little.succ_double (to_little_uint p)
      | p~0 => Little.double (to_little_uint p)
      end.

    Definition to_uint p := rev (to_little_uint p).

  Module Export String.
    Fixpoint of_uint (v : uint) : string
      := match v with
         | Nil => ""
         | D0 x => String "0" (of_uint x)
         | D1 x => String "1" (of_uint x)
         | D2 x => String "2" (of_uint x)
         | D3 x => String "3" (of_uint x)
         | D4 x => String "4" (of_uint x)
         | D5 x => String "5" (of_uint x)
         | D6 x => String "6" (of_uint x)
         | D7 x => String "7" (of_uint x)
         | D8 x => String "8" (of_uint x)
         | D9 x => String "9" (of_uint x)
         end.

Definition decimal_string_of_pos (p : positive) : string
  := String.of_uint (Pos.to_uint p).

Definition decimal_string_of_Z (v : Z) : string
  := match v with
     | Zpos p => decimal_string_of_pos p
     | Z0 => "0"
     | Zneg p => String "-" (decimal_string_of_pos p)
     end.

Import Coq.NArith.BinNat.
Local Open Scope string_scope.

Class Show T := show : bool -> T -> string.

Definition maybe_wrap_parens (parens : bool) (s : string)
  := if parens then "(" ++ s ++ ")" else s.

Global Instance show_unit : Show unit := fun _ _ => "tt".
Global Instance show_bool : Show bool := fun _ b => if b then "true" else "false".
  Global Instance show_positive : Show positive
    := fun _ p
       => decimal_string_of_pos p.
  Global Instance show_N : Show N
    := fun _ n
       => match n with
         | N0 => "0"
         | Npos p => show false p
         end.
  Global Instance show_nat : Show nat
    := fun _ n => show false (N.of_nat n).

Module Export Hex.
  Definition show_Z : Show Z
    := fun _ z => HexString.of_Z z.

Definition bind {A B} (v : option A) (f : A -> option B) : option B
  := match v with
     | Some v => f v
     | None => None
     end.
  Delimit Scope option_scope with option.

  Notation "A <- X ; B" := (bind X (fun A => B%option)) : option_scope.

Module Export ZRange.
Import Coq.ZArith.ZArith.

Record zrange := { lower : Z ; upper : Z }.
Bind Scope zrange_scope with zrange.

Definition is_tighter_than_bool (x y : zrange) : bool
  := ((lower y <=? lower x) && (upper x <=? upper y))%bool%Z.
  Notation "r[ l ~> u ]" := {| lower := l ; upper := u |} : zrange_scope.

Global Instance show_zrange : Show zrange
  := fun _ r
     => "[" ++ Hex.show_Z false (lower r) ++ " ~> " ++ Hex.show_Z false (upper r) ++ "]".

Module Export Language.

Module Export Compilers.
  Module Export type.
    Inductive type (base_type : Type) := base (t : base_type) | arrow (s d : type base_type).
    Global Arguments base {_}.
    Global Arguments arrow {_} s d.

    Fixpoint for_each_lhs_of_arrow {base_type} (f : type base_type -> Type) (t : type base_type) : Type
      := match t with
         | base t => unit
         | arrow s d => f s * @for_each_lhs_of_arrow _ f d
         end.

    Fixpoint interp {base_type} (base_interp : base_type -> Type) (t : type base_type) : Type
      := match t with
         | base t => base_interp t
         | arrow s d => @interp _ base_interp s -> @interp _ base_interp d
         end.

    End type.
  Delimit Scope etype_scope with etype.
  Bind Scope etype_scope with type.type.
  Infix "->" := type.arrow : etype_scope.
  Module base.
    Module Export type.
      Inductive base := unit | Z | bool | nat.

      Inductive type := type_base (t : base) | prod (A B : type) | list (A : type).
    End type.
    Notation type := type.type.
    Definition base_interp (ty : type.base)
      := match ty with
         | type.unit => Datatypes.unit
         | type.Z => BinInt.Z
         | type.bool => Datatypes.bool
         | type.nat => Datatypes.nat
         end.
    Fixpoint interp (ty : type)
      := match ty with
         | type.type_base t => base_interp t
         | type.prod A B => interp A * interp B
         | type.list A => Datatypes.list (interp A)
         end%type.
  End base.
  Global Coercion base.type.type_base : base.type.base >-> base.type.type.
  Bind Scope etype_scope with base.type.
  Infix "*" := base.type.prod : etype_scope.

  Module Export expr.
    Section with_var.
      Context {base_type : Type}.
      Local Notation type := (type base_type).
      Context {ident : type -> Type}
              {var : type -> Type}.

      Inductive expr : type -> Type :=
      | Ident {t} (idc : ident t) : expr t
      | Var {t} (v : var t) : expr t
      | Abs {s d} (f : var s -> expr d) : expr (s -> d)
      | App {s d} (f : expr (s -> d)) (x : expr s) : expr d
      | LetIn {A B} (x : expr A) (f : var A -> expr B) : expr B
      .
    End with_var.

    Module Export Notations.
      Delimit Scope expr_scope with expr.
      Delimit Scope expr_pat_scope with expr_pat.
    End Notations.
  End expr.

  Module ident.
    Local Notation type := (type base.type).
    Local Notation ttype := type.
    Section with_base.
      Let type_base (x : base.type) : type := type.base x.
      Local Coercion type_base : base.type >-> type.
      Section with_scope.
        Import base.type.
        Notation type := ttype.

        Inductive ident : type -> Type :=
        | Literal {t:base.type.base} (v : base.interp t) : ident t
        | Nat_succ : ident (nat -> nat)
        | Nat_pred : ident (nat -> nat)
        | Nat_max : ident (nat -> nat -> nat)
        | Nat_mul : ident (nat -> nat -> nat)
        | Nat_add : ident (nat -> nat -> nat)
        | Nat_sub : ident (nat -> nat -> nat)
        | nil {t} : ident (list t)
        | cons {t:base.type} : ident (t -> list t -> list t)
        | pair {A B:base.type} : ident (A -> B -> A * B)
        | fst {A B} : ident (A * B -> A)
        | snd {A B} : ident (A * B -> B)
        | pair_rect {A B T:base.type} : ident ((A -> B -> T) -> A * B -> T)
        | bool_rect {T:base.type} : ident ((unit -> T) -> (unit -> T) -> bool -> T)
        | nat_rect {P:base.type} : ident ((unit -> P) -> (nat -> P -> P) -> nat -> P)
        | list_rect {A P:base.type} : ident ((unit -> P) -> (A -> list A -> P -> P) -> list A -> P)
        | list_case {A P:base.type} : ident ((unit -> P) -> (A -> list A -> P) -> list A -> P)
        | List_length {T} : ident (list T -> nat)
        | List_seq : ident (nat -> nat -> list nat)
        | List_repeat {A:base.type} : ident (A -> nat -> list A)
        | List_combine {A B} : ident (list A -> list B -> list (A * B))
        | List_map {A B:base.type} : ident ((A -> B) -> list A -> list B)
        | List_app {A} : ident (list A -> list A -> list A)
        | List_rev {A} : ident (list A -> list A)
        | List_flat_map {A B:base.type} : ident ((A -> (list B)) -> list A -> (list B))
        | List_partition {A:base.type} : ident ((A -> bool) -> list A -> (list A * list A))
        | List_fold_right {A B:base.type} : ident ((B -> A -> A) -> A -> list B -> A)
        | List_update_nth {T:base.type} : ident (nat -> (T -> T) -> list T -> list T)
        | List_nth_default {T:base.type} : ident (T -> list T -> nat -> T)
        | Z_add : ident (Z -> Z -> Z)
        | Z_mul : ident (Z -> Z -> Z)
        | Z_pow : ident (Z -> Z -> Z)
        | Z_sub : ident (Z -> Z -> Z)
        | Z_opp : ident (Z -> Z)
        | Z_div : ident (Z -> Z -> Z)
        | Z_modulo : ident (Z -> Z -> Z)
        | Z_log2 : ident (Z -> Z)
        | Z_log2_up : ident (Z -> Z)
        | Z_eqb : ident (Z -> Z -> bool)
        | Z_leb : ident (Z -> Z -> bool)
        | Z_geb : ident (Z -> Z -> bool)
        | Z_of_nat : ident (nat -> Z)
        | Z_to_nat : ident (Z -> nat)
        | Z_shiftr : ident (Z -> Z -> Z)
        | Z_shiftl : ident (Z -> Z -> Z)
        | Z_land : ident (Z -> Z -> Z)
        | Z_lor : ident (Z -> Z -> Z)
        | Z_bneg : ident (Z -> Z)
        | Z_lnot_modulo : ident (Z -> Z -> Z)
        | Z_mul_split : ident (Z -> Z -> Z -> Z * Z)
        | Z_add_get_carry : ident (Z -> Z -> Z -> (Z * Z))
        | Z_add_with_carry : ident (Z -> Z -> Z -> Z)
        | Z_add_with_get_carry : ident (Z -> Z -> Z -> Z -> (Z * Z))
        | Z_sub_get_borrow : ident (Z -> Z -> Z -> (Z * Z))
        | Z_sub_with_get_borrow : ident (Z -> Z -> Z -> Z -> (Z * Z))
        | Z_zselect : ident (Z -> Z -> Z -> Z)
        | Z_add_modulo : ident (Z -> Z -> Z -> Z)
        | Z_rshi : ident (Z -> Z -> Z -> Z -> Z)
        | Z_cc_m : ident (Z -> Z -> Z)
        | Z_cast (range : zrange) : ident (Z -> Z)
        | Z_cast2 (range : zrange * zrange) : ident ((Z * Z) -> (Z * Z))
        | fancy_add (log2wordmax : BinInt.Z) (imm : BinInt.Z) : ident (Z * Z -> Z * Z)
        | fancy_addc (log2wordmax : BinInt.Z) (imm : BinInt.Z) : ident (Z * Z * Z -> Z * Z)
        | fancy_sub (log2wordmax : BinInt.Z) (imm : BinInt.Z) : ident (Z * Z -> Z * Z)
        | fancy_subb (log2wordmax : BinInt.Z) (imm : BinInt.Z) : ident (Z * Z * Z -> Z * Z)
        | fancy_mulll (log2wordmax : BinInt.Z) : ident (Z * Z -> Z)
        | fancy_mullh (log2wordmax : BinInt.Z) : ident (Z * Z -> Z)
        | fancy_mulhl (log2wordmax : BinInt.Z) : ident (Z * Z -> Z)
        | fancy_mulhh (log2wordmax : BinInt.Z) : ident (Z * Z -> Z)
        | fancy_rshi (log2wordmax : BinInt.Z) : BinInt.Z -> ident (Z * Z -> Z)
        | fancy_selc : ident (Z * Z * Z -> Z)
        | fancy_selm (log2wordmax : BinInt.Z) : ident (Z * Z * Z -> Z)
        | fancy_sell : ident (Z * Z * Z -> Z)
        | fancy_addm : ident (Z * Z * Z -> Z)
        .
      End with_scope.

      End with_base.

    End ident.
  Notation ident := ident.ident.

  Module Import invert_expr.
    Module Export ident.

      Definition invert_Literal {t} (idc : ident t) : option (type.interp base.interp t)
        := match idc with
           | ident.Literal _ n => Some n
           | _ => None
           end.
    End ident.

    Section with_var.
      Context {var : type base.type -> Type}.
      Local Notation expr := (@expr base.type ident var).
      Definition invert_Literal {t} (e : expr t)
        : option (type.interp base.interp t)
        := match e with
           | expr.Ident _ idc => ident.invert_Literal idc
           | _ => None
           end%expr_pat%expr.
    End with_var.
  End invert_expr.

  Module Import defaults.
    Notation type := (type base.type).
    Global Coercion type_base (t : base.type) : type := type.base t.
  End defaults.

  End Compilers.

End Language.
Import Coq.Bool.Bool.
Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Module Compilers.
  Import invert_expr.
  Import defaults.

  Module Export ToString.
    Local Open Scope string_scope.

    Module Export PHOAS.
      Module type.
        Module Export base.
          Global Instance show_base : Show base.type.base
            := fun _ t => match t with
                       | base.type.unit => "()"
                       | base.type.Z => "ℤ"
                       | base.type.bool => "𝔹"
                       | base.type.nat => "ℕ"
                       end.
          Fixpoint show_type (with_parens : bool) (t : base.type) : string
            := match t with
               | base.type.type_base t => show with_parens t
               | base.type.prod A B => maybe_wrap_parens
                                        with_parens
                                        (@show_type false A ++ " * " ++ @show_type true B)
               | base.type.list A => "[" ++ @show_type false A ++ "]"
               end.
          Global Instance show : Show base.type := show_type.
        End base.

        Fixpoint show_type {base_type} {S : Show base_type} (with_parens : bool) (t : type.type base_type) : string
          := match t with
             | type.base t => S with_parens t
             | type.arrow s d
               => maybe_wrap_parens
                   with_parens
                   (@show_type base_type S true s ++ " → " ++ @show_type base_type S false d)
             end.
        Global Instance show {base_type} {S : Show base_type} : Show (type.type base_type) := show_type.
      End type.

      Module Export ident.
        Definition show_range_or_ctype (v : zrange) : string
          := if (v.(lower) =? 0) && (v.(upper) =? 2^(Z.log2 (v.(upper) + 1)) - 1)
             then ("uint" ++ decimal_string_of_Z (Z.log2 (v.(upper) + 1)) ++ "_t")%string
             else let lg2 := 1 + Z.log2 (-v.(lower)) in
                  if (v.(lower) =? -2^(lg2-1)) && (v.(upper) =? 2^(lg2-1)-1)
                  then ("int" ++ decimal_string_of_Z lg2 ++ "_t")%string
                  else show false v.
        Definition show_compact_Z (with_parens : bool) (v : Z) : string
          := let is_neg := v <? 0 in
             (if is_neg then "-" else "")
               ++ (let v := Z.abs v in
                   (if v <=? 2^8
                    then decimal_string_of_Z v
                    else if v =? 2^(Z.log2 v)
                         then "2^" ++ (decimal_string_of_Z (Z.log2 v))
                         else if v =? 2^(Z.log2_up v) - 1
                              then maybe_wrap_parens is_neg ("2^" ++ (decimal_string_of_Z (Z.log2_up v)) ++ "-1")
                              else Hex.show_Z with_parens v)).
        Global Instance show_ident {t} : Show (ident.ident t)
          := fun with_parens idc
             => match idc with
                | ident.Literal base.type.Z v => show_compact_Z with_parens v
                | ident.Literal t v => show with_parens v
                | ident.Nat_succ => "Nat.succ"
                | ident.Nat_pred => "Nat.pred"
                | ident.Nat_max => "Nat.max"
                | ident.Nat_mul => "Nat.mul"
                | ident.Nat_add => "Nat.add"
                | ident.Nat_sub => "Nat.sub"
                | ident.nil t => "[]"
                | ident.cons t => "(::)"
                | ident.pair A B => "(,)"
                | ident.fst A B => "fst"
                | ident.snd A B => "snd"
                | ident.pair_rect A B T => "pair_rect"
                | ident.bool_rect T => "bool_rect"
                | ident.nat_rect P => "nat_rect"
                | ident.list_rect A P => "list_rect"
                | ident.list_case A P => "list_case"
                | ident.List_length T => "length"
                | ident.List_seq => "seq"
                | ident.List_repeat A => "repeat"
                | ident.List_combine A B => "combine"
                | ident.List_map A B => "map"
                | ident.List_app A => "(++)"
                | ident.List_rev A => "rev"
                | ident.List_flat_map A B => "flat_map"
                | ident.List_partition A => "partition"
                | ident.List_fold_right A B => "fold_right"
                | ident.List_update_nth T => "update_nth"
                | ident.List_nth_default T => "nth"
                | ident.Z_add => "(+)"
                | ident.Z_mul => "( * )"
                | ident.Z_pow => "(^)"
                | ident.Z_sub => "(-)"
                | ident.Z_opp => "-"
                | ident.Z_div => "(/)"
                | ident.Z_modulo => "(mod)"
                | ident.Z_eqb => "(=)"
                | ident.Z_leb => "(≤)"
                | ident.Z_geb => "(≥)"
                | ident.Z_log2 => "log₂"
                | ident.Z_log2_up => "⌈log₂⌉"
                | ident.Z_of_nat => "(ℕ→ℤ)"
                | ident.Z_to_nat => "(ℤ→ℕ)"
                | ident.Z_shiftr => "(>>)"
                | ident.Z_shiftl => "(<<)"
                | ident.Z_land => "(&)"
                | ident.Z_lor => "(|)"
                | ident.Z_lnot_modulo => "~"
                | ident.Z_bneg => "!"
                | ident.Z_mul_split => "Z.mul_split"
                | ident.Z_add_get_carry => "Z.add_get_carry"
                | ident.Z_add_with_carry => "Z.add_with_carry"
                | ident.Z_add_with_get_carry => "Z.add_with_get_carry"
                | ident.Z_sub_get_borrow => "Z.sub_get_borrow"
                | ident.Z_sub_with_get_borrow => "Z.sub_with_get_borrow"
                | ident.Z_zselect => "Z.zselect"
                | ident.Z_add_modulo => "Z.add_modulo"
                | ident.Z_rshi => "Z.rshi"
                | ident.Z_cc_m => "Z.cc_m"
                | ident.Z_cast range => "(" ++ show_range_or_ctype range ++ ")"
                | ident.Z_cast2 (r1, r2) => "(" ++ show_range_or_ctype r1 ++ ", " ++ show_range_or_ctype r2 ++ ")"
                | ident.fancy_add log2wordmax imm
                  => maybe_wrap_parens with_parens ("fancy.add 2^" ++ decimal_string_of_Z log2wordmax ++ " " ++ HexString.of_Z imm)
                | ident.fancy_addc log2wordmax imm
                  => maybe_wrap_parens with_parens ("fancy.addc 2^" ++ decimal_string_of_Z log2wordmax ++ " " ++ HexString.of_Z imm)
                | ident.fancy_sub log2wordmax imm
                  => maybe_wrap_parens with_parens ("fancy.sub 2^" ++ decimal_string_of_Z log2wordmax ++ " " ++ HexString.of_Z imm)
                | ident.fancy_subb log2wordmax imm
                  => maybe_wrap_parens with_parens ("fancy.subb 2^" ++ decimal_string_of_Z log2wordmax ++ " " ++ HexString.of_Z imm)
                | ident.fancy_mulll log2wordmax
                  => maybe_wrap_parens with_parens ("fancy.mulll 2^" ++ decimal_string_of_Z log2wordmax)
                | ident.fancy_mullh log2wordmax
                  => maybe_wrap_parens with_parens ("fancy.mullh 2^" ++ decimal_string_of_Z log2wordmax)
                | ident.fancy_mulhl log2wordmax
                  => maybe_wrap_parens with_parens ("fancy.mulhl 2^" ++ decimal_string_of_Z log2wordmax)
                | ident.fancy_mulhh log2wordmax
                  => maybe_wrap_parens with_parens ("fancy.mulhh 2^" ++ decimal_string_of_Z log2wordmax)
                | ident.fancy_rshi log2wordmax x
                  => maybe_wrap_parens with_parens ("fancy.rshi 2^" ++ decimal_string_of_Z log2wordmax ++ " " ++ decimal_string_of_Z x)
                | ident.fancy_selc => "fancy.selc"
                | ident.fancy_selm log2wordmax
                  => maybe_wrap_parens with_parens ("fancy.selm 2^" ++ decimal_string_of_Z log2wordmax)
                | ident.fancy_sell => "fancy.sell"
                | ident.fancy_addm => "fancy.addm"
                end.
      End ident.

      Module Export expr.
        Section with_base_type.
          Context {base_type} {ident : type.type base_type -> Type}
                  {show_base_type : Show base_type}
                  {show_ident : forall t, Show (ident t)}.
          Fixpoint show_var_expr {var t} (with_parens : bool) (e : @expr.expr base_type ident var t) : string
            := match e with
               | expr.Ident t idc => show with_parens idc
               | expr.Var t v => maybe_wrap_parens with_parens ("VAR_(" ++ show false t ++ ")")
               | expr.Abs s d f => "λ_(" ++ show false t ++ ")"
               | expr.App s d f x
                 => let show_f := @show_var_expr _ _ false f in
                    let show_x := @show_var_expr _ _ true x in
                    maybe_wrap_parens with_parens (show_f ++ " @ " ++ show_x)
               | expr.LetIn A B x f
                 => let show_x := @show_var_expr _ _ false x in
                    maybe_wrap_parens with_parens ("expr_let _ := " ++ show_x ++ " in _")
               end%string.
          Definition partially_show_expr {var t} : Show (@expr.expr base_type ident var t) := show_var_expr.
        End with_base_type.
      End expr.
    End PHOAS.

    Module Export C.
      Module type.
        Inductive primitive := Z | Zptr.
        Inductive type := type_primitive (t : primitive) | prod (A B : type) | unit.
        Module Export Notations.
          Global Coercion type_primitive : primitive >-> type.

          Bind Scope Ctype_scope with type.
          Notation "A * B" := (prod A B) : Ctype_scope.
          Notation type := type.
        End Notations.
      End type.
      Import type.Notations.

      Module int.
        Inductive type := signed (lgbitwidth : nat) | unsigned (lgbitwidth : nat).

        Definition lgbitwidth_of (t : type) : nat
          := match t with
             | signed lgbitwidth => lgbitwidth
             | unsigned lgbitwidth => lgbitwidth
             end.
        Definition bitwidth_of (t : type) : Z := 2^Z.of_nat (lgbitwidth_of t).
        Definition is_signed (t : type) : bool := match t with signed _ => true | unsigned _ => false end.
        Definition is_unsigned (t : type) : bool := negb (is_signed t).
        Definition to_zrange (t : type) : zrange
          := let bw := bitwidth_of t in
             if is_signed t
             then r[-2^bw ~> 2^(bw-1) - 1]
             else r[0 ~> 2^bw - 1].

        Global Instance show_type : Show type
          := fun with_parens t
             => maybe_wrap_parens
                 with_parens
                 ((if is_unsigned t then "u" else "") ++ "int" ++ decimal_string_of_Z (bitwidth_of t)).

        End int.

      Section ident.
        Import type.
        Inductive ident : type -> type -> Set :=
        | literal (v : BinInt.Z) : ident unit Z
        | List_nth (n : Datatypes.nat) : ident Zptr Z
        | Addr : ident Z Zptr
        | Dereference : ident Zptr Z
        | Z_shiftr (offset : BinInt.Z) : ident Z Z
        | Z_shiftl (offset : BinInt.Z) : ident Z Z
        | Z_land : ident (Z * Z) Z
        | Z_lor : ident (Z * Z) Z
        | Z_add : ident (Z * Z) Z
        | Z_mul : ident (Z * Z) Z
        | Z_sub : ident (Z * Z) Z
        | Z_opp : ident Z Z
        | Z_lnot (ty:int.type) : ident Z Z
        | Z_bneg : ident Z Z
        | Z_mul_split (lgs:BinInt.Z) : ident ((Zptr * Zptr) * (Z * Z)) unit
        | Z_add_with_get_carry (lgs:BinInt.Z) : ident ((Zptr * Zptr) * (Z * Z * Z)) unit
        | Z_sub_with_get_borrow (lgs:BinInt.Z) : ident ((Zptr * Zptr) * (Z * Z * Z)) unit
        | Z_zselect (ty:int.type) : ident (Zptr * (Z * Z * Z)) unit
        | Z_add_modulo : ident (Z * Z * Z) Z
        | Z_static_cast (ty : int.type) : ident Z Z
        .
      End ident.

      Inductive arith_expr : type -> Set :=
      | AppIdent {s d} (idc : ident s d) (arg : arith_expr s) : arith_expr d
      | Var (t : type.primitive) (v : string) : arith_expr t
      | Pair {A B} (a : arith_expr A) (b : arith_expr B) : arith_expr (A * B)
      | TT : arith_expr type.unit.

      Inductive stmt :=
      | Call (val : arith_expr type.unit)
      | Assign (declare : bool) (t : type.primitive) (sz : option int.type) (name : string) (val : arith_expr t)
      | AssignZPtr (name : string) (sz : option int.type) (val : arith_expr type.Z)
      | DeclareVar (t : type.primitive) (sz : option int.type) (name : string)
      | AssignNth (name : string) (n : nat) (val : arith_expr type.Z).
      Definition expr := list stmt.

      Module Export Notations.
        Delimit Scope Cexpr_scope with Cexpr.
        Infix "@@" := AppIdent : Cexpr_scope.
        Notation "( x , y , .. , z )" := (Pair .. (Pair x%Cexpr y%Cexpr) .. z%Cexpr) : Cexpr_scope.
      End Notations.

      Module Export OfPHOAS.
        Fixpoint base_var_data (t : base.type) : Set
          := match t with
             | base.type.unit
               => unit
             | base.type.nat
             | base.type.bool
               => Empty_set
             | base.type.Z => string * option int.type
             | base.type.prod A B => base_var_data A * base_var_data B
             | base.type.list A => string * option int.type * nat
             end.
        Definition var_data (t : Compilers.type.type base.type) : Set
          := match t with
             | type.base t => base_var_data t
             | type.arrow s d => Empty_set
             end.

        Local Notation ErrT T := (T + list string)%type.
        Local Notation ret v := (@inl _ (list string) v) (only parsing).
        Reserved Notation "A1 ,, A2 <- X1 , X2 ; B" (at level 70, A2 at next level, right associativity, format "'[v' A1 ,,  A2  <-  X1 ,  X2 ; '/' B ']'").
        Reserved Notation "A1 ,, A2 ,, A3 ,, A4 <- X1 , X2 , X3 , X4 ; B" (at level 70, A2 at next level, A3 at next level, A4 at next level, right associativity, format "'[v' A1 ,,  A2 ,,  A3 ,,  A4  <-  X1 ,  X2 ,  X3 ,  X4 ; '/' B ']'").
        Local Definition bind2_err {A B C} (v1 : ErrT A) (v2 : ErrT B) (f : A -> B -> ErrT C) : ErrT C
          := match v1, v2 with
              | inl x1, inl x2 => f x1 x2
              | inr err, inl _ | inl _, inr err => inr err
              | inr err1, inr err2 => inr (List.app err1 err2)
              end.
        Local Notation "x1 ,, x2 <- v1 , v2 ; f"
          := (bind2_err v1 v2 (fun x1 x2 => f)).
        Local Definition bind4_err {A B C D R} (v1 : ErrT A) (v2 : ErrT B) (v3 : ErrT C) (v4 : ErrT D) (f : A -> B -> C -> D -> ErrT R) : ErrT R
          := (x12 ,, x34 <- (x1 ,, x2 <- v1, v2; inl (x1, x2)), (x3 ,, x4 <- v3, v4; inl (x3, x4));
                let '((x1, x2), (x3, x4)) := (x12, x34) in
                f x1 x2 x3 x4).
        Local Notation "x1 ,, x2 ,, x3 ,, x4 <- v1 , v2 , v3 , v4 ; f"
          := (bind4_err v1 v2 v3 v4 (fun x1 x2 x3 x4 => f)).

        Definition maybe_log2 (s : Z) : option Z
          := if 2^Z.log2 s =? s then Some (Z.log2 s) else None.

        Definition bounds_check (descr : string) {t} (idc : ident.ident t) (s : BinInt.Z) {t'} (ev : @Compilers.expr.expr base.type ident.ident var_data t') (found : option int.type)
          : ErrT unit
          := let _ := @PHOAS.expr.partially_show_expr in
             match found with
             | None => inr ["Missing range on " ++ descr ++ " " ++ show true idc ++ ": " ++ show true ev]%string
             | Some ty
               => if ZRange.is_tighter_than_bool (int.to_zrange ty) r[0~>2^s-1]
                 then ret tt
                 else inr ["Final bounds check failed on " ++ descr ++ " " ++ show false idc ++ "; expected an unsigned " ++ decimal_string_of_Z s ++ "-bit number, but found a " ++ show false ty ++ "."]%string
             end.
        Axiom admit : forall {T}, T.

        Definition recognize_3arg_2ref_ident
                   (t:=(base.type.Z -> base.type.Z -> base.type.Z -> base.type.Z * base.type.Z)%etype)
                   (idc : ident.ident t)
                   (rout : option int.type * option int.type)
                   (args : type.for_each_lhs_of_arrow (fun t => @Compilers.expr.expr base.type ident.ident var_data t * (arith_expr type.Z * option int.type))%type t)
          : ErrT (arith_expr (type.Zptr * type.Zptr) -> expr)
          := let _ := @PHOAS.expr.partially_show_expr in
             let '((s, _), ((e1v, (e1, r1)), ((e2v, (e2, r2)), tt))) := args in
             match (s <- invert_Literal s; maybe_log2 s)%option, idc return ErrT (arith_expr (type.Zptr * type.Zptr) -> expr)
             with
             | Some s, _
               => (_ ,, _ ,, _ ,, _
                    <- bounds_check "" idc s e1v r1,
                  bounds_check "" idc s e2v r2,
                  bounds_check "" idc s e2v (fst rout),
                  bounds_check "" idc s e2v (snd rout);
                     inl (fun retptr => [Call (Z_mul_split s @@ (retptr, (e1, e2)))%Cexpr]))
             | _, _ => admit end.

      End OfPHOAS.
    End C.
  End ToString.
End Compilers.
End ZRange.
End Hex.
End String.
End Pos.
End Little.
End HexString.

Require Export Coq.extraction.Extraction.
Require Export Coq.extraction.ExtrOcamlBasic.
Require Export Coq.extraction.ExtrOcamlString.
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Import ListNotations. Local Open Scope string_scope.

Global Set Warnings Append "-extraction".
Extraction Language Ocaml.
Global Unset Extraction Optimize.

Redirect "bug_bad_extraction.ml" Recursive Extraction Compilers.ToString.C.OfPHOAS.recognize_3arg_2ref_ident.
