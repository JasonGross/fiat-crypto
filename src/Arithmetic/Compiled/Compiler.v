Require Import Coq.Numbers.BinNums Coq.ZArith.BinInt.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Compilers.Tuple.
Require Import Crypto.Compilers.Wf.
Require Crypto.Compilers.Inline.
Require Crypto.Compilers.Named.Context.
Require Crypto.Compilers.Named.Syntax.
Require Crypto.Compilers.Named.InterpretToPHOAS.
Require Crypto.Compilers.Named.Compile.
Require Crypto.Compilers.Named.PositiveContext.
Require Crypto.Compilers.Named.PositiveContext.Defaults.
Require Import Crypto.Compilers.SmartMap.
Require Crypto.Compilers.StripExpr.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.ZExtended.Syntax.
Require Import Crypto.Compilers.ZExtended.MapBaseType.
Import ZUtil.Definitions.
Require Import Crypto.Util.Curry.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.ZExtended.InlineConstAndOp.
Require Import Crypto.Compilers.ZExtended.InlineConstAndOpByRewrite.
Require Import Crypto.Compilers.Linearize.
Require Import Crypto.Compilers.Eta.
Import Crypto.Util.ZUtil.Definitions Crypto.Util.ZUtil.CPS Crypto.Util.IdfunWithAlt.
Require Import Crypto.Util.Tactics.Head.

Local Notation exprZ
  := (@Syntax.exprf
        ZExtended.Syntax.base_type
        ZExtended.Syntax.op).
Local Notation tZ := (Tbase TZ).
Local Notation tBool := (Tbase TBool).
Inductive ZOrExpr (var : base_type -> Type) (t : flat_type base_type) :=
| inI (_ : interp_flat_type interp_base_type t)
| inExpr (_ : @exprZ var t).
Arguments inExpr {_ _} _.
Arguments inI {_ _} _.
Definition inZ {var} (v : Z) : ZOrExpr var tZ := inI (t:=tZ) v.
Arguments inZ / .

Local Coercion exprOfZOrExpr {var t} (v : ZOrExpr var t) : @exprZ var t
  := match v with
     | inI v => SmartMap.SmartPairf (SmartMap.SmartVarfMap (fun t v => Op (Const v) TT) v)
     | inExpr v => v
     end.

Definition PairZOrExpr {var A B} (a : @ZOrExpr var A) (b : @ZOrExpr var B)
  : @ZOrExpr var (A * B)
  := match a, b with
     | inI a, inI b => inI (t:=A*B) (a, b)
     | a, b => inExpr (Pair (exprOfZOrExpr a) (exprOfZOrExpr b))
     end.
Fixpoint ZOrExprSmartPairf {var t} : interp_flat_type (fun t => @ZOrExpr var (Tbase t)) t -> ZOrExpr var t
  := match t with
     | Tbase T => fun v => v
     | Unit => fun v => inI (t:=Unit) tt
     | Prod A B
       => fun ab : interp_flat_type _ A * interp_flat_type _ B
          => PairZOrExpr (@ZOrExprSmartPairf var A (fst ab))
                         (@ZOrExprSmartPairf var B (snd ab))
     end.

Ltac refresh x :=
  let maybe_x := fresh x in
  let maybe_x := fresh x in
  let maybe_x := fresh x in
  let not_x := fresh x in
  not_x.

Ltac fix_arg ty arg :=
  lazymatch ty with
  | ?A -> ?B
    => let arg' := fresh "arg" in
       (eval cbv beta zeta in
           (fun a : A
            => let arg' := arg a in
               ltac:(let v := fix_arg B arg' in exact v)))
  | @exprZ ?var' tZ
    => constr:(Op (var:=var') (ConstZ (arg : interp_flat_type interp_base_type tZ)) TT
               : interp_flat_type (fun t => @exprZ var' (Tbase t)) tZ)
  | @ZOrExpr ?var' tZ
    => constr:(inZ (arg : interp_flat_type interp_base_type tZ)
               : interp_flat_type (fun t => @ZOrExpr var' (Tbase t)) tZ)
  | (?A * ?B)%type
    => let arg' := open_constr:(_) in
       let arg1 := open_constr:(fst arg') in
       let arg2 := open_constr:(snd arg') in
       let arg1 := fix_arg A arg1 in
       let arg2 := fix_arg B arg2 in
       let ret := constr:((arg1, arg2)) in
       lazymatch type of arg' with
       | (interp_flat_type ?var ?A * interp_flat_type ?var ?B)%type
         => let unif := constr:(eq_refl : arg' = arg :> interp_flat_type var (Prod A B)) in
            ret
       | ?T => let dummy := match goal with _ => idtac "Warning: fix_arg: Unhandled type" T "(A :=" A ", B :=" B ", ret :=" ret ")" end in
               ret
       end
  | Tuple.tuple (?f (Tbase TZ)) ?n'
    => constr:(flat_interp_tuple (interp_base_type:=fun ty' => f (Tbase ty')) (T:=tZ) (n:=n') arg)
  | list ?A
    => constr:(List.map
                 (fun arg' => ltac:(let v := fix_arg A arg' in exact v))
                 arg)
  | _ => constr:(arg : ty)
  end.
Ltac fix_args t :=
  lazymatch type of t with
  | ?A -> ?B
    => let x := fresh "x" in
       (eval cbv beta zeta in
           (fun x => ltac:(let x' := fix_arg A x in
                           let v := fix_args (t x') in
                           exact v)))
  | _ => t
  end.

Definition of_tupleZ {var : base_type -> Type} {n : nat} (ts : Tuple.tuple Z n)
  : interp_flat_type _ (Syntax.tuple _ n)
  := flat_interp_untuple (n:=n) (interp_base_type:=interp_base_type) (T:=tZ) ts.

Definition of_tuple_var {var : base_type -> Type} {n : nat} (ts : Tuple.tuple (@ZOrExpr var tZ) n)
  := ZOrExprSmartPairf (flat_interp_untuple (n:=n) (interp_base_type:=fun ty' => @ZOrExpr var (Tbase ty')) (T:=tZ) ts).

Local Definition failb : forall var t, @Syntax.exprf base_type op var (Tbase t)
  := fun var t
     => match t with
        | TZ => Syntax.Op (ConstZ 0%Z) Syntax.TT
        | Tbool => Syntax.Op (ConstBool true) Syntax.TT
        end.

Local Notation PContext var := (PositiveContext.PositiveContext _ var _ internal_base_type_dec_bl).

Definition OpZOrExpr {var} {s d} (f : op s d)
           (args : @ZOrExpr var s)
  : @ZOrExpr var d
  := match args with
     | inI x => inI (interp_op f x)
     | inExpr x => inExpr (Op f x)
     end.

Local Notation lift1 f :=
  (fun x => OpZOrExpr f x).
Local Notation lift2 f :=
  (fun x y => OpZOrExpr f (PairZOrExpr x y)).
Local Notation lift3 f :=
  (fun x y z => OpZOrExpr f (PairZOrExpr (PairZOrExpr x y) z)).
Local Notation lift1e f :=
  (fun x => inExpr (Op f (exprOfZOrExpr x))).
Local Notation lift2e f :=
  (fun x y => inExpr (Op f (exprOfZOrExpr (PairZOrExpr x y)))).
Local Notation lift3e f :=
  (fun x y z => inExpr (Op f (exprOfZOrExpr (PairZOrExpr (PairZOrExpr x y) z)))).

Definition BoolCaseZOrExpr {var T} (b : @ZOrExpr var tBool) (t f : @ZOrExpr var T)
  : @ZOrExpr var T
  := match b with
     | inI b
       => if b then t else f
     | inExpr x as b
       => OpZOrExpr BoolCase (PairZOrExpr (PairZOrExpr b t) f)
     end.

Definition IdWithAltZOrExpr {var T} (x y : @ZOrExpr var (Tbase T))
  : @ZOrExpr var (Tbase T)
  := match x, y with
     | inI x, inI y
       => inI (id_with_alt x y)
     | x, y
       => OpZOrExpr IdWithAlt (PairZOrExpr x y)
     end.

Definition IdTupleWithAltZOrExpr {var n T} (x y : Tuple.tuple (@ZOrExpr var (Tbase T)) n)
  : Tuple.tuple (@ZOrExpr var (Tbase T)) n
  := Tuple.map2 IdWithAltZOrExpr x y.

Definition IdTupleWithAltZOrExpr_cps {var n R} (T:=TZ)
           (x y : forall R, (Tuple.tuple (@ZOrExpr var (Tbase T)) n -> R) -> R)
           (f : Tuple.tuple (@ZOrExpr var (Tbase T)) n -> @ZOrExpr var R)
  : @ZOrExpr var R.
  refine match invert_Pairs (x _ of_tuple_var), invert_Pairs (y _ of_tuple_var) with
         | Some x, Some y
           => f (Tuple.map2 (fun x y => inExpr (Op IdWithAlt (Pair x y)))
                            (flat_interp_tuple x)
                            (flat_interp_tuple y))
         | Some _, None
         | None, Some _
         | None, None
           => _
         end.
  refine (let g := _ in
          let k := (LetIn (OpZOrExpr IdWithAlt (PairZOrExpr (x _ of_tuple_var) (y _ of_tuple_var)))
                          (fun v => f (g v))) in _).
  cbn in *.
  pose

Definition MulSplitZOrExpr {var} (bitwidth : @ZOrExpr var tZ) (x y : @ZOrExpr var tZ)
  : @ZOrExpr var (tZ * tZ)
  := match bitwidth with
     | inI bitwidth
       => OpZOrExpr (MulSplitAtBitwidthZ bitwidth) (PairZOrExpr x y)
     | inExpr _ as bitwidth
       => OpZOrExpr MulSplitAtBitwidth (PairZOrExpr (PairZOrExpr bitwidth x) y)
     end.
Definition AddWithGetCarryZOrExpr {var} (bitwidth : @ZOrExpr var tZ) (x y z : @ZOrExpr var tZ)
  : @ZOrExpr var (tZ * tZ)
  := match bitwidth with
     | inI bitwidth
       => OpZOrExpr (AddWithGetCarryZ bitwidth) (PairZOrExpr (PairZOrExpr x y) z)
     | inExpr _ as bitwidth
       => OpZOrExpr AddWithGetCarry (PairZOrExpr (PairZOrExpr (PairZOrExpr bitwidth x) y) z)
     end.

Definition SubWithGetBorrowZOrExpr {var} (bitwidth : @ZOrExpr var tZ) (x y z : @ZOrExpr var tZ)
  : @ZOrExpr var (tZ * tZ)
  := match bitwidth with
     | inI bitwidth
       => OpZOrExpr (SubWithGetBorrowZ bitwidth) (PairZOrExpr (PairZOrExpr x y) z)
     | inExpr _ as bitwidth
       => OpZOrExpr SubWithGetBorrow (PairZOrExpr (PairZOrExpr (PairZOrExpr bitwidth x) y) z)
     end.

Ltac under_nat_binders tac term :=
  let T := type of term in
  lazymatch eval hnf in T with
  | forall a : nat, _
    => constr:(fun a : nat => ltac:(let v := under_nat_binders tac (term a) in exact v))
  | _
    => let term := (eval cbv beta in term) in
       tac term
  end.

(*Ltac find_expr_type term found not_found :=
  let check_expr :=
      ltac:(fun t
            =>
              lazymatch t with
              | @ZOrExpr ?var ?tz => constr:(Some t)
              | _ => let dummy := match goal with _ => idtac "bad" t end in
                     constr:(I : I)
              end) in
  let T := match (eval cbv beta in term) with
           | context[@LetIn.Let_In Z (fun _ => ?T)]
             => check_expr T
           | context[@LetIn.Let_In (Z * Z) (fun _ => ?T)]
             => check_expr T
           | context [@Z.add_get_carry_cps ?T]
             => check_expr T
           | context [@Z.add_with_get_carry_cps ?T]
             => check_expr T
           | context [@Z.sub_get_borrow_cps ?T]
             => check_expr T
           | context [@Z.sub_with_get_borrow_cps ?T]
             => check_expr T
           | context [@Z.mul_split_at_bitwidth_cps ?T]
             => check_expr T
           | context [@Z.eqb_cps ?T]
             => check_expr T
           | context [@id_with_alt ?T]
             => check_expr T
           | _ => constr:(@None unit)
           end in
  lazymatch T with
  | Some ?T => found T
  | None => not_found ()
  end.
*)
Ltac unfold_id_with_alt_unit t :=
  lazymatch t with
  | context T[@id_with_alt unit]
    => let c := constr:(@id_with_alt unit) in
       let c' := (eval compute in c) in
       let t := context T[c'] in
       let t := (eval cbv beta in t) in
       unfold_id_with_alt_unit t
  | context T[@id_with_alt (Tuple.tuple' ?t 0)]
    => let c := constr:(@id_with_alt (Tuple.tuple' t 0)) in
       let c' := (eval compute in c) in
       let t := context T[c'] in
       let t := (eval cbv beta in t) in
       unfold_id_with_alt_unit t
  | _ => t
  end.

Ltac with_pattern_consts middle_tac t :=
  let update_t z_val t
      := let t := (eval pattern z_val in t) in
         let t := lazymatch t with ?t _ => t end in
         let t := with_pattern_consts middle_tac t in
         let t := constr:(t (inZ z_val)) in
         t in
  lazymatch t with
  | context[Z.pos ?p] => update_t (Z.pos p) t
  | _ => middle_tac t
  end.

Ltac with_patterned_Z var t tac :=
  let t := (eval
              pattern
              (@Z.zselect),
            @runtime_mul, @runtime_add, @runtime_opp, @runtime_shr, @runtime_and, @runtime_lor,
            Z.mul, Z.add, Z.sub, Z.opp, Z.shiftr, Z.shiftl, Z.land, Z.lor,
            Z.modulo, Z.div, Z.log2, Z.pow, Z.ones, Z.of_nat,
            2%Z, 1%Z, 0%Z
             in t) in
  let t := match t with ?t
                         _
                         _ _ _ _ _ _
                         _ _ _ _ _ _ _ _
                         _ _ _ _ _ _
                         _ _ _
                        => t end in
  let mid_tac t :=
      ltac:(
        let t := (eval pattern Z,
                  (@Z.add_get_carry_cps), (@Z.add_with_get_carry_cps),
                  (@Z.sub_get_borrow_cps), (@Z.sub_with_get_borrow_cps),
                  (@Z.mul_split_at_bitwidth_cps),
                  (@Z.eqb_cps) in t) in
        let t := match t with ?t _ _ _ _ _ _ _ => t end in
        let t := match t with (fun P : Set => ?t) => constr:(fun P : Type => t) end in
        let work_around_issue_5996 := type of t in
        let t := (eval cbv beta in (t (@ZOrExpr var tZ))) in
        let Zadd_get_carry_cps         := fresh "Zadd_get_carry_cps" in
        let Zadd_with_get_carry_cps    := fresh "Zadd_with_get_carry_cps" in
        let Zsub_get_borrow_cps        := fresh "Zsub_get_borrow_cps" in
        let Zsub_with_get_borrow_cps   := fresh "Zsub_with_get_borrow_cps" in
        let Zmul_split_at_bitwidth_cps := fresh "Zmul_split_at_bitwidth_cps" in
        let Zeqb_cps                   := fresh "Zmul_split_at_bitwidth_cps" in
        let t :=
            constr:(
              fun
                Zadd_get_carry_cps
                Zadd_with_get_carry_cps
                Zsub_get_borrow_cps
                Zsub_with_get_borrow_cps
                Zmul_split_at_bitwidth_cps
                Zeqb_cps
              => ltac:(let t := (eval cbv beta in (t
                                                     Zadd_get_carry_cps
                                                     Zadd_with_get_carry_cps
                                                     Zsub_get_borrow_cps
                                                     Zsub_with_get_borrow_cps
                                                     Zmul_split_at_bitwidth_cps
                                                     Zeqb_cps)) in
                       let t := tac
                                  t
                                  Zadd_get_carry_cps
                                  Zadd_with_get_carry_cps
                                  Zsub_get_borrow_cps
                                  Zsub_with_get_borrow_cps
                                  Zmul_split_at_bitwidth_cps
                                  Zeqb_cps in
                       exact t)
            ) in
        let t := (eval cbv beta zeta in t) in
        let dummy := match goal with _ => idtac "AAA" t end in
        let t := match t with fun _ _ _ _ _ _ => ?t => t end in
        let dummy := match goal with _ => idtac "BBB" t end in
        t
      ) in
  let t := with_pattern_consts mid_tac t in
  let t := constr:(t
                     (lift3e Zselect)
                     (lift2e Zmul) (lift2e Zadd) (lift1e Zopp) (lift2e Zshiftr) (lift2e Zland) (lift2e Zlor)
                     (lift2 Zmul) (lift2 Zadd) (lift2 Zsub) (lift1 Zopp) (lift2 Zshiftr) (lift2 Zshiftl) (lift2 Zland) (lift2 Zlor)
                     (lift2 Zmodulo) (lift2 Zdiv) (lift1 Zlog2) (lift2 Zpow) (lift1 Zones)
                     (fun n => inZ (Z.of_nat n))
                     (inZ 2%Z) (inZ 1%Z) (inZ 0%Z)
                     (fun ts => (*under_cps_post_compile*) (of_tuple_var ts))) in
  t.

Ltac do_pattern_strip_replace_with SmartVarVarf var T t
     Zadd_get_carry_cps
     Zadd_with_get_carry_cps
     Zsub_get_borrow_cps
     Zsub_with_get_borrow_cps
     Zmul_split_at_bitwidth_cps
     Zeqb_cps :=
  let Z := constr:(@ZOrExpr var tZ) in
  let t := (eval pattern
                 (@LetIn.Let_In Z (fun _ => T)),
            (@LetIn.Let_In (Z * Z) (fun _ => T)),
            (@Zadd_get_carry_cps T), (@Zadd_with_get_carry_cps T),
            (@Zsub_get_borrow_cps T), (@Zsub_with_get_borrow_cps T),
            (@Zmul_split_at_bitwidth_cps T),
            (@Zeqb_cps T)
             in t) in
  let t := match t with ?t
                         _
                         _
                         _ _
                         _ _
                         _
                         _
                        => t end in
  let t :=
      constr:(
        let var' := (fun ty => @ZOrExpr var (Tbase ty)) in
        let f_type := interp_flat_type var' (Prod tZ tZ) -> _ in
        let t'
            := t
                 (fun v' f => inExpr (LetIn (exprOfZOrExpr v') (fun args => exprOfZOrExpr (f (SmartVarVarf args)))))
                 (fun v' f => inExpr (LetIn (exprOfZOrExpr (fst v')) (fun v'0 => LetIn (exprOfZOrExpr (snd v')) (fun v'1 => exprOfZOrExpr (f (SmartVarVarf v'0, SmartVarVarf v'1))))))
                 (fun x y z (f : f_type) => inExpr (LetIn (exprOfZOrExpr (AddWithGetCarryZOrExpr x (@inI _ tZ 0%Z) y z))
                                                          (fun args => exprOfZOrExpr (f (SmartVarVarf args)))))
                 (fun x y z w (f : f_type) => inExpr (LetIn (exprOfZOrExpr (AddWithGetCarryZOrExpr x y z w))
                                                            (fun args => exprOfZOrExpr (f (SmartVarVarf args)))))
                 (fun x y z (f : f_type) => inExpr (LetIn (exprOfZOrExpr (SubWithGetBorrowZOrExpr x (@inI _ tZ 0%Z) y z))
                                                          (fun args => exprOfZOrExpr (f (SmartVarVarf args)))))
                 (fun x y z w (f : f_type) => inExpr (LetIn (exprOfZOrExpr (SubWithGetBorrowZOrExpr x y z w))
                                                            (fun args => exprOfZOrExpr (f (SmartVarVarf args)))))
                 (fun x y z (f : f_type) => inExpr (LetIn (exprOfZOrExpr (MulSplitZOrExpr x y z))
                                                          (fun args => exprOfZOrExpr (f (SmartVarVarf args)))))
                 (fun x y f => BoolCaseZOrExpr (OpZOrExpr Zeqb (PairZOrExpr x y)) (f true) (f false)) in
        t') in
  let t := (eval cbv beta zeta in t) in
  t.

Ltac find_expr_type Z
     Zadd_get_carry_cps
     Zadd_with_get_carry_cps
     Zsub_get_borrow_cps
     Zsub_with_get_borrow_cps
     Zmul_split_at_bitwidth_cps
     Zeqb_cps
     term found not_found :=
  let check_expr :=
      ltac:(fun t
            =>
              lazymatch t with
              | @ZOrExpr ?var ?tz => constr:(Some t)
              | _ => let dummy := match goal with _ => idtac "bad" t end in
                     constr:(I : I)
              end) in
  let T := match (eval cbv beta in term) with
           | context[@LetIn.Let_In Z (fun _ => ?T)]
             => check_expr T
           | context[@LetIn.Let_In (Z * Z) (fun _ => ?T)]
             => check_expr T
           | context [@Zadd_get_carry_cps ?T]
             => check_expr T
           | context [@Zadd_with_get_carry_cps ?T]
             => check_expr T
           | context [@Zsub_get_borrow_cps ?T]
             => check_expr T
           | context [@Zsub_with_get_borrow_cps ?T]
             => check_expr T
           | context [@Zmul_split_at_bitwidth_cps ?T]
             => check_expr T
           | context [@Zeqb_cps ?T]
             => check_expr T
           | context [@id_with_alt ?T]
             => check_expr T
           | _ => constr:(@None unit)
           end in
  lazymatch T with
  | Some ?T => found T
  | None => not_found ()
  end.


Ltac do_pattern_strip_replace SmartVarVarf var t
     Zadd_get_carry_cps
     Zadd_with_get_carry_cps
     Zsub_get_borrow_cps
     Zsub_with_get_borrow_cps
     Zmul_split_at_bitwidth_cps
     Zeqb_cps :=
  let Z := constr:(@ZOrExpr var tZ) in
  let do_find := ltac:(find_expr_type
                         Z
                         Zadd_get_carry_cps
                         Zadd_with_get_carry_cps
                         Zsub_get_borrow_cps
                         Zsub_with_get_borrow_cps
                         Zmul_split_at_bitwidth_cps
                         Zeqb_cps) in
  let rec_call t :=
      ltac:(do_pattern_strip_replace
              SmartVarVarf var t
              Zadd_get_carry_cps
              Zadd_with_get_carry_cps
              Zsub_get_borrow_cps
              Zsub_with_get_borrow_cps
              Zmul_split_at_bitwidth_cps
              Zeqb_cps) in
  do_find
    t
    ltac:(fun T => let t := do_pattern_strip_replace_with
                              SmartVarVarf var T t
                              Zadd_get_carry_cps
                              Zadd_with_get_carry_cps
                              Zsub_get_borrow_cps
                              Zsub_with_get_borrow_cps
                              Zmul_split_at_bitwidth_cps
                              Zeqb_cps in
                   rec_call t)
           ltac:(fun _ => t).

Ltac do_sanity_check t :=
  let t := (eval pattern (@LetIn.Let_In), (@id_with_alt), (@CPSUtil.id_tuple_with_alt_cps), (@id_tuple_with_alt) in t) in
  let t := match t with ?t _ _ _ _ => t end in
  let dummy := match goal with _ => idtac "presanity" t end in
  let t := match t with fun _ _ _ _ => ?t => t end in
  let dummy := match goal with _ => idtac "sane" end in
  t.
Check @CPSUtil.id_tuple_with_alt_cps _ _ _.
Check @IdTupleWithAltZOrExpr_cps _ _ _.
    cbn.
  pose (option_map flat_interp_tuple ()).
  pose (of_tuple_var (Tuple.map2 IdWithAltZOrExpr (x _ id) (y _ id)))
  pose (@of_tuple_var).
  :=
Ltac do_pattern_strip_replace_id_with_alt SmartVarVarf var t :=
  let rec_call := ltac:(do_pattern_strip_replace_id_with_alt SmartVarVarf var) in
  lazymatch t with
  | context[@CPSUtil.id_tuple_with_alt_cps (ZOrExpr ?var ?T) (ZOrExpr ?var (Tbase ?tz)) ?n]
    => let dummy := match goal with _ => idtac "prepatterna" R A n end in
       let t := (eval pattern (@CPSUtil.id_tuple_with_alt_cps (ZOrExpr var T) (ZOrExpr var (Tbase tz)) n) in t) in
       let t := match t with ?t _ => t end in
       let t := (eval cbv [IdTupleWithAltZOrExpr_cps]
                      constr:(t
  | _ => t
  end.

Ltac do_pattern_Z SmartVarVarf var t :=
  with_patterned_Z
    var t
    ltac:(fun
             t
             Zadd_get_carry_cps
             Zadd_with_get_carry_cps
             Zsub_get_borrow_cps
             Zsub_with_get_borrow_cps
             Zmul_split_at_bitwidth_cps
             Zeqb_cps
           => let t := do_pattern_strip_replace_id_with_alt
                         SmartVarVarf var t in
              let t := do_pattern_strip_replace
                         SmartVarVarf var t
                         Zadd_get_carry_cps
                         Zadd_with_get_carry_cps
                         Zsub_get_borrow_cps
                         Zsub_with_get_borrow_cps
                         Zmul_split_at_bitwidth_cps
                         Zeqb_cps in
              let t := do_sanity_check t in
              t).

Ltac compile varf SmartVarVarf t :=
  let exprZf := constr:(fun var n => (@ZOrExpr (varf var) (tuple tZ n))) in
  let t := (eval cbv beta zeta in
               ltac:(let v := fresh in
                     pose t as v;
                     repeat autounfold with basesystem_partial_evaluation_unfolder in v;
                     let v := (eval cbv delta [v] in v) in
                     exact v)) in
  let t := (eval cbv [
                   B.limb ListUtil.sum ListUtil.sum_firstn
                          CPSUtil.Tuple.mapi_with_cps CPSUtil.Tuple.mapi_with'_cps CPSUtil.flat_map_cps CPSUtil.on_tuple_cps CPSUtil.fold_right_cps2
                          Decidable.dec Decidable.dec_eq_Z
                          id_tuple_with_alt id_tuple'_with_alt
                          Z.add_get_carry_full Z.mul_split
                          Z.add_get_carry_full_cps Z.mul_split_cps Z.mul_split_cps'
                          Z.sub_with_get_borrow_full_cps
                          Z.sub_get_borrow_full_cps
                          Z.add_with_get_carry_full
                          Z.add_with_get_carry_full_cps
                 ] in t) in
  let t
      := constr:(
           fun (var : base_type -> Type)
           => ltac:(
                let t
                    := under_nat_binders
                         ltac:(
                         fun t
                         => let t := do_pattern_Z SmartVarVarf var t in
                            let t := fix_args t in
                            exact t)
                                (t var)
                in
                exact t)) in
  let t := (eval cbv beta iota zeta in t) in
  t.


Definition post_compile {n} {src} (t : forall var : base_type -> Type, interp_flat_type (fun t => @ZOrExpr var (Tbase t)) src -> @ZOrExpr var (tZ ^ n))
  := let t := fun var => Syntax.Abs (fun args => t var (SmartMap.SmartVarfMap (fun t v => inExpr (Var v)) args)) in
     dlet t := Linearize (InlineConstAndOp.InlineConstAndOp t) in
     let t := MapBaseType t in
     option_map
       (fun t
        => let t := Linearize t in
           let t := ExprEta t in
           t)
       t.

Ltac post_compile t :=
  let t := (eval cbv [post_compile] in (post_compile t)) in
  let t := (eval cbn [domain codomain fst snd] in t) in
  t.

Ltac do_compile_sig op_cps appf :=
  eexists;
  let SmartVarVarf := uconstr:(fun v => SmartMap.SmartVarfMap (fun t => inExpr) (SmartMap.SmartVarVarf v)) in
  let varf := uconstr:(fun var => var) in
  let t_ty := type of op_cps in
  let t := lazymatch (eval cbv beta zeta in t_ty) with
           | forall (n : nat) (R : Type) (f : Tuple.tuple Z (@?n_expr n) -> R), _
             => compile varf SmartVarVarf (fun var n => op_cps n (@ZOrExpr (varf var) (tuple tZ (n_expr n))))
           | forall (n1 n2 : nat) (R : Type) (f : Tuple.tuple Z (@?n_expr n1 n2) -> R), _
             => compile varf SmartVarVarf (fun var n1 n2 => op_cps n1 n2 (@ZOrExpr (varf var) (tuple tZ (n_expr n1 n2))))
           | forall (n : nat) (R : Type) (m : nat) (f : Tuple.tuple Z (@?n_expr n) -> R), _
             => compile varf SmartVarVarf (fun var n => op_cps n (@ZOrExpr (varf var) (tuple tZ (n_expr n))))
           | ?T
             => let dummy := match goal with _ => idtac "Warning: do_compile_sig: Unsupported type" T end in
                compile varf SmartVarVarf (fun var n => op_cps n (@ZOrExpr (varf var) (tuple tZ n)))
           end in
  let t := post_compile (fun var => appf (t var)) in
  exact t.

Declare Reduction compiler_preprered
  := cbv [id
            CPSUtil.map_cps List.seq InlineConstAndOp.InlineConstAndOp Compilers.Syntax.tuple Tuple.repeat Tuple.append domain codomain ExprEta expr_eta expr_eta_gen interp_flat_type_eta_gen Syntax.tuple' Linearize InlineConstAndOp Compilers.InlineConstAndOp.InlineConstAndOp Linearize_gen Inline.InlineConstGen linearize_gen Inline.inline_const_gen ExprInversion.invert_Abs SmartMap.SmartVarfMap SmartMap.SmartVarVarf flat_interp_tuple CPSUtil.to_list_cps CPSUtil.to_list_cps' CPSUtil.to_list'_cps CPSUtil.combine_cps Nat.pred List.app CPSUtil.from_list_default_cps CPSUtil.update_nth_cps CPSUtil.from_list_default'_cps Tuple.map SmartMap.SmartPairf Tuple.map' flat_interp_untuple flat_interp_untuple' of_tuple_var flat_interp_untuple flat_interp_untuple' SmartMap.SmartPairf tuple tuple' linearizef ZOrExprSmartPairf inZ BoolCaseZOrExpr MulSplitZOrExpr AddWithGetCarryZOrExpr SubWithGetBorrowZOrExpr CPSUtil.fold_right_cps2_specialized SmartMap.SmartVarfMap SmartMap.SmartPairf MapBaseType Compilers.MapBaseType.MapBaseType MapBaseType.check_map_base_type Compilers.MapBaseType.MapBaseType' MapBaseType.map_base_type MapBaseType.check_map_base_type_gen].

Ltac do_prered t :=
  let t' := head t in
  let t := (eval cbv delta [t'] in t) in
  let t := (eval compiler_preprered in t) in
  exact t.

Notation compiler_prered t := ltac:(do_prered t) (only parsing).
