Require Import Crypto.Arithmetic.CoreUnfolder.
Require Import Crypto.Arithmetic.Saturated.FreezeUnfolder.
Import BinNums BinInt ZArith LetIn.


Require Import Crypto.Compilers.Tuple.
Require Import Crypto.Compilers.Wf.
Require Crypto.Compilers.Inline.
Require Crypto.Compilers.Named.Context.
Require Crypto.Compilers.Named.Syntax.
Require Crypto.Compilers.Named.InterpretToPHOAS.
Require Crypto.Compilers.Named.Compile.
Require Crypto.Compilers.Named.PositiveContext.
Require Crypto.Compilers.Named.PositiveContext.Defaults.
Require Crypto.Compilers.SmartMap.
Require Crypto.Compilers.StripExpr.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.ZExtended.Syntax.
(*Require Import Crypto.Compilers.InSet.Syntax.
Require Import Crypto.Compilers.InSet.Typeify.*)
Import ZUtil.Definitions.
Require Import Crypto.Util.Curry.
Import Arithmetic.Core ZUtil.Definitions ZUtil.CPS Util.IdfunWithAlt.

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
Coercion exprOfZOrExpr {var t} (v : ZOrExpr var t) : @exprZ var t
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

Ltac fix_arg ty arg :=
  lazymatch ty with
  | ?A -> ?B
    => let arg' := fresh "arg" in
       (eval cbv beta zeta in
           (fun a : A
            => let arg' := arg a in
               ltac:(let v := fix_arg B arg' in exact v)))
  | @exprZ ?var' tZ
    => constr:(Op (var:=var') (ConstZ arg) TT
               : interp_flat_type (fun t => @exprZ var' (Tbase t)) tZ)
  | @ZOrExpr ?var' tZ
    => constr:(inZ arg
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
       | ?T => let dummy := match goal with _ => idtac "Warning: fix_arg: Unhandled type" T end in
               ret
       end
  | Tuple.tuple (?f (Tbase TZ)) ?n'
    => constr:(flat_interp_tuple (interp_base_type:=fun ty' => f (Tbase ty')) (T:=tZ) (n:=n') arg)
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

Definition of_tuple_var {var : base_type -> Type} {n : nat} (ts : Tuple.tuple (@ZOrExpr var tZ) n)
  := ZOrExprSmartPairf (flat_interp_untuple (n:=n) (interp_base_type:=fun ty' => @ZOrExpr var (Tbase ty')) (T:=tZ) ts).
(*Definition of_tuple_var {var : base_type -> Type} {n : nat} (ts : Tuple.tuple (@exprZ var tZ) n)
  := SmartMap.SmartPairf (flat_interp_untuple (n:=n) (interp_base_type:=fun ty' => @Compilers.Syntax.exprf _ op var (Tbase ty')) (T:=tZ) ts).*)
Check of_tuple_var.
Require Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.ZExtended.InlineConstAndOp.
Require Import Crypto.Compilers.ZExtended.InlineConstAndOpByRewrite.
Require Import Crypto.Compilers.Linearize.
Require Import Crypto.Compilers.Eta.

Definition under_cps_post_compile {var T} (v : @exprZ var T)
  : @exprZ var T
  := let t := linearizef (inline_const_and_opf v) in
     let t := exprf_eta t in
     t.



(*Definition of_tuple_var {var : base_type -> Type} {n : nat} (ts : Tuple.tuple (var TZ) n)
  := SmartMap.SmartPairf (flat_interp_untuple (n:=n) (interp_base_type:=fun ty' => @Compilers.Syntax.exprf _ op var (Tbase ty')) (T:=tZ) (Tuple.map Compilers.Syntax.Var ts)).*)
(*Definition of_tuple_var {var : base_type -> Set} {n : nat} (ts : Tuple.tuple (var TZ) n)
  := untypeify (SmartMap.SmartPairf (flat_interp_untuple (n:=n) (interp_base_type:=fun ty' => @Compilers.Syntax.exprf _ op var (Tbase ty')) (T:=tZ) (Tuple.map Compilers.Syntax.Var ts))).*)

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

Ltac compile varf extraVar SmartVarVarf t :=
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
                 ] in t) in
  let t
      := constr:(
           fun (var : base_type -> Type) (n : nat)
           => ltac:(
                let t := (eval cbv beta in (t var n)) in
                let T := (eval cbv beta in (exprZf var n)) in
                let t := (eval
                            pattern
                            (@LetIn.Let_In Z (fun _ => T)),
                          (@LetIn.Let_In (Z * Z) (fun _ => T)),
                          (@Z.add_get_carry_cps T),
                          (@Z.mul_split_at_bitwidth_cps T),
                          (@Z.eqb_cps T),
                          (@Z.zselect),
                          @runtime_mul, @runtime_add, @runtime_opp, @runtime_shr, @runtime_and, @runtime_lor,
                          Z.mul, Z.add, Z.opp, Z.shiftr, Z.shiftl, Z.land, Z.lor,
                          Z.modulo, Z.div, Z.log2, Z.pow, Z.ones,
                          2%Z, 1%Z, 0%Z

                           in t) in
                let t := match t with ?t
                                       _
                                       _
                                       _
                                       _
                                       _
                                       _
                                       _ _ _ _ _ _
                                       _ _ _ _ _ _ _
                                       _ _ _ _ _
                                       _ _ _
                                      => t end in
                let t := (eval pattern Z, (@LetIn.Let_In), (@id_with_alt), (@Z.add_get_carry_cps), (@Z.mul_split_at_bitwidth_cps), (@Z.eqb_cps) in t) in
                let t := match t with ?t _ _ _ _ _ _ => t end in
                let t := match t with fun P _ _ _ _ _ => @?t P => t end in
                let t := match t with (fun P : Set => ?t) => constr:(fun P : Type => t) end in
                let work_around_issue_5996 := type of t in
                exact t)) in
  let t := (eval cbv beta iota zeta in
               (fun var n
                => let var' := (fun ty => @ZOrExpr var (Tbase ty)) in
                   let f_type := interp_flat_type var' (Prod tZ tZ) -> _ in
                   let t'
                       := t var n (@ZOrExpr var tZ)
                            (fun v' f => inExpr (LetIn (extraVar v') (fun args => f (SmartVarVarf args))))
                            (fun v' f => inExpr (LetIn (extraVar (fst v')) (fun v'0 => LetIn (extraVar (snd v')) (fun v'1 => f (SmartVarVarf v'0, SmartVarVarf v'1)))))
                            (fun x y z (f : f_type) => inExpr (LetIn (var:=varf var) (inExpr (Op AddGetCarry (Pair (Pair (extraVar x) (extraVar y)) (extraVar z)))) (fun args => f (SmartVarVarf args))))
                            (fun x y z (f : f_type) => inExpr (LetIn (var:=varf var) (Op MulSplitAtBitwidth (Pair (Pair (extraVar x) (extraVar y)) (extraVar z))) (fun args => f (SmartVarVarf args))))
                            (fun x y f => BoolCaseZOrExpr (OpZOrExpr Zeqb (PairZOrExpr (extraVar x) (extraVar y))) (f true) (f false))
                            (lift3e Zselect)
                            (lift2e Zmul) (lift2e Zadd) (lift1e Zopp) (lift2e Zshiftr) (lift2e Zland) (lift2e Zlor)
                            (lift2 Zmul) (lift2 Zadd) (lift1 Zopp) (lift2 Zshiftr) (lift2 Zshiftl) (lift2 Zland) (lift2 Zlor)
                            (lift2 Zmodulo) (lift2 Zdiv) (lift1 Zlog2) (lift2 Zpow) (lift1 Zones)
                            (inZ 2%Z) (inZ 1%Z) (inZ 0%Z)
                            (fun ts => (*under_cps_post_compile*) (of_tuple_var (Tuple.map extraVar ts))) in
               ltac:(let v := fix_args t' in exact v)
           )) in
  t.


Definition post_compile {n} {src} (t : forall var : base_type -> Type, interp_flat_type (fun t => @ZOrExpr var (Tbase t)) src -> @ZOrExpr var (tZ ^ n))
  := let t := fun var => Syntax.Abs (fun args => t var (SmartMap.SmartVarfMap (fun t v => inExpr (Var v)) args)) in
     let t := Linearize (InlineConstAndOp.InlineConstAndOp t) in
     let t := ExprEta t in
     t.

Ltac post_compile t :=
  let t := (eval cbv [post_compile] in (post_compile t)) in
  let t := (eval cbn [domain codomain] in t) in
  t.


Definition compiled_preadd_sig (weight : nat -> Z) (n : nat)
  : { t : _ & t }.
Proof.
  eexists. (* (fun t => @exprZ var (Tbase t)) *)
  let SmartVarVarf := uconstr:(fun v => SmartMap.SmartVarfMap (fun t => inExpr) (SmartMap.SmartVarVarf v)) in
  let extraVar := uconstr:(fun v => v) in
  let varf := uconstr:(fun var => var) in
  let t := compile varf extraVar SmartVarVarf (fun var n f weight xy => @Core.B.Positional.add_cps weight n (fst xy) (snd xy) (@ZOrExpr (varf var) (tuple tZ n)) f) in
  let t := post_compile (fun var xy => t var n weight xy) in
  exact t.
Defined.

Definition compiled_preadd wt n
  := Eval cbv [projT2 projT1 compiled_preadd_sig] in
      projT2 (compiled_preadd_sig wt n).

(*
Definition compiled_premul_sig (weight : nat -> Z) (n : nat)
  : { t : _ & t }.
Proof.
  eexists. (* (fun t => @exprZ var (Tbase t)) *)
  let SmartVarVarf := uconstr:(fun v => SmartMap.SmartVarfMap (fun t => inExpr) (SmartMap.SmartVarVarf v)) in
  let extraVar := uconstr:(fun v => v) in
  let varf := uconstr:(fun var => var) in
  let t := compile varf extraVar SmartVarVarf (fun var n m f weight xy => @Core.B.Positional.mul_cps weight n (n*2-1)%nat (fst xy) (snd xy) (@ZOrExpr (varf var) (tuple tZ n)) f) in
  let t := post_compile (fun var xy => t var n weight xy) in
  exact t.
Defined.

Definition compiled_premul wt n
  := Eval cbv [projT2 projT1 compiled_premul_sig] in
      projT2 (compiled_premul_sig wt n).
 *)
Locate freeze_cps.
Print Freeze.freeze_cps.
Definition compiled_prefreeze_sig (weight : nat -> Z) (n : nat) (bitwidth : Z)
  : { t : _ & t }.
Proof.
  eexists. (* (fun t => @exprZ var (Tbase t)) *)
  let SmartVarVarf := uconstr:(fun v => SmartMap.SmartVarfMap (fun t => inExpr) (SmartMap.SmartVarVarf v)) in
  let extraVar := uconstr:(fun v => v) in
  let varf := uconstr:(fun var => var) in
  let t := compile varf extraVar SmartVarVarf (fun var n f weight mask xy => @Freeze.freeze_cps weight n mask (fst xy) (snd xy) (@ZOrExpr (varf var) (tuple tZ n)) f) in
  let t := post_compile (fun var xy => t var n weight (Z.ones bitwidth) xy) in
  exact t.
Defined.

Definition compiled_prefreeze wt n bitwidth
  := Eval cbv [projT2 projT1 compiled_prefreeze_sig] in
      projT2 (compiled_prefreeze_sig wt n bitwidth).



Require Import Crypto.Specific.Framework.SynthesisFramework.
Require Import Crypto.Specific.X25519.C64.Synthesis.
Declare Reduction compiler_red0 := cbv [CPSUtil.map_cps List.seq InlineConstAndOp.InlineConstAndOp Compilers.Syntax.tuple Tuple.repeat Tuple.append domain codomain ExprEta expr_eta expr_eta_gen interp_flat_type_eta_gen Syntax.tuple' Linearize InlineConstAndOp Compilers.InlineConstAndOp.InlineConstAndOp Linearize_gen Inline.InlineConstGen linearize_gen Inline.inline_const_gen ExprInversion.invert_Abs SmartMap.SmartVarfMap SmartMap.SmartVarVarf flat_interp_tuple CPSUtil.to_list_cps CPSUtil.to_list_cps' CPSUtil.to_list'_cps CPSUtil.combine_cps Nat.pred List.app CPSUtil.from_list_default_cps CPSUtil.update_nth_cps CPSUtil.from_list_default'_cps Tuple.map SmartMap.SmartPairf Tuple.map' flat_interp_untuple flat_interp_untuple' of_tuple_var flat_interp_untuple flat_interp_untuple' SmartMap.SmartPairf tuple tuple' under_cps_post_compile linearizef ZOrExprSmartPairf inZ BoolCaseZOrExpr CPSUtil.fold_right_cps2_specialized SmartMap.SmartVarfMap SmartMap.SmartPairf].
Declare Reduction compiler_red1 := vm_compute.
Time Definition compiled_add
  := ltac:(let v := constr:(compiled_preadd wt sz) in
           let v := (eval cbv [compiled_preadd P.sz] in v) in
           let v := (eval compiler_red0 in v) in
           let v := (eval compiler_red1 in v) in
           exact v).
Time Definition compiled_freeze
  := ltac:(let v := constr:(compiled_prefreeze wt sz bitwidth) in
           let v := (eval cbv [compiled_prefreeze P.sz] in v) in
           let v := (eval compiler_red0 in v) in
           let v := (eval compiler_red1 in v) in
           exact v).
convtactic.
Definition compiled_add' := compiled_preadd wt sz.
Definition compiled_add2 := Eval
    in compiled_add'.
Timeout 5 Time Definition compiled_add := Eval vm_compute in compiled_add2.
Print compiled_add.
(*Arguments compiled_add2 / .
Definition compiled_add3 := Eval cbn [compiled_add2 flat_interp_tuple' SmartMap.smart_interp_flat_map fst snd PairZOrExpr exprOfZOrExpr OpZOrExpr interp_op curry2 SmartMap.smart_interp_flat_map] in compiled_add2.
Arguments compiled_add3 / .
Goal True.
  Set Printing Depth 100000.
(*pose (fun xy => @Core.B.Positional.add_cps wt sz (fst xy) (snd xy)) as e.
    cbv [compiled_add compiled_preadd P.sz CPSUtil.map_cps List.seq InlineConstAndOp.InlineConstAndOp Compilers.Syntax.tuple Tuple.repeat Tuple.append domain codomain ExprEta expr_eta expr_eta_gen interp_flat_type_eta_gen Syntax.tuple' Linearize InlineConstAndOp Compilers.InlineConstAndOp.InlineConstAndOp Linearize_gen Inline.InlineConstGen linearize_gen Inline.inline_const_gen ExprInversion.invert_Abs SmartMap.SmartVarfMap SmartMap.SmartVarVarf flat_interp_tuple CPSUtil.to_list_cps CPSUtil.to_list_cps' CPSUtil.to_list'_cps CPSUtil.combine_cps Nat.pred List.app CPSUtil.from_list_default_cps CPSUtil.update_nth_cps CPSUtil.from_list_default'_cps Tuple.map SmartMap.SmartPairf Tuple.map' flat_interp_untuple flat_interp_untuple' of_tuple_var flat_interp_untuple flat_interp_untuple' SmartMap.SmartPairf tuple tuple' under_cps_post_compile linearizef ZOrExprSmartPairf inZ] in e;
    cbn [flat_interp_tuple' SmartMap.smart_interp_flat_map fst snd] in e.
  cbv [CPSUtil.fold_right_cps2_specialized] in e.
  cbv [B.Positional.add_cps B.Positional.to_associational_cps CPSUtil.map_cps List.seq CPSUtil.to_list_cps CPSUtil.to_list_cps' CPSUtil.to_list'_cps CPSUtil.combine_cps B.Positional.from_associational_cps B.Positional.place_cps B.Positional.add_to_nth_cps CPSUtil.on_tuple_cps CPSUtil.update_nth_cps CPSUtil.from_list_default_cps CPSUtil.from_list_default'_cps B.Positional.zeros Tuple.repeat Tuple.append Nat.pred CPSUtil.fold_right_cps2 CPSUtil.fold_right_cps2_specialized List.app] in e.
  cbn [fst snd] in e.
  unfold CPSUtil.fold_right_cps2_specialized_step at 1 in (value of e); cbn [fst snd] in e.
  *)
  pose compiled_add as e.
  Set Printing Depth 100000.
  cbv [compiled_add compiled_preadd P.sz CPSUtil.map_cps List.seq InlineConstAndOp.InlineConstAndOp Compilers.Syntax.tuple Tuple.repeat Tuple.append domain codomain ExprEta expr_eta expr_eta_gen interp_flat_type_eta_gen Syntax.tuple' Linearize InlineConstAndOp Compilers.InlineConstAndOp.InlineConstAndOp Linearize_gen Inline.InlineConstGen linearize_gen Inline.inline_const_gen ExprInversion.invert_Abs SmartMap.SmartVarfMap SmartMap.SmartVarVarf flat_interp_tuple CPSUtil.to_list_cps CPSUtil.to_list_cps' CPSUtil.to_list'_cps CPSUtil.combine_cps Nat.pred List.app CPSUtil.from_list_default_cps CPSUtil.update_nth_cps CPSUtil.from_list_default'_cps Tuple.map SmartMap.SmartPairf Tuple.map' flat_interp_untuple flat_interp_untuple' of_tuple_var flat_interp_untuple flat_interp_untuple' SmartMap.SmartPairf tuple tuple' under_cps_post_compile linearizef ZOrExprSmartPairf inZ BoolCaseZOrExpr] in e;
    cbn [flat_interp_tuple' SmartMap.smart_interp_flat_map fst snd] in e.
  cbv [CPSUtil.fold_right_cps2_specialized] in e.
  About CPSUtil.fold_right_cps2_specialized_step.
  Local Notation frcss := (@CPSUtil.fold_right_cps2_specialized_step _ _ _ _ _).
  unfold CPSUtil.fold_right_cps2_specialized_step at 1 in (value of e); cbn [fst snd] in e.
  cbn [PairZOrExpr exprOfZOrExpr OpZOrExpr interp_op curry2] in e;
    cbv [SmartMap.SmartVarfMap SmartMap.SmartPairf] in e;
    cbn [PairZOrExpr exprOfZOrExpr OpZOrExpr interp_op curry2 SmartMap.smart_interp_flat_map] in e.
  repeat match eval cbv delta [e] in e with
         | context[Z.eqb ?x ?y]
           => set (k := Z.eqb x y) in (value of e);
                vm_compute in k; subst k
         end.
  cbv beta iota in e.
  unfold CPSUtil.fold_right_cps2_specialized_step at 1 in (value of e); cbn [fst snd] in e.
  cbn [PairZOrExpr exprOfZOrExpr OpZOrExpr interp_op curry2] in e;
    cbv [SmartMap.SmartVarfMap SmartMap.SmartPairf] in e;
    cbn [PairZOrExpr exprOfZOrExpr OpZOrExpr interp_op curry2 SmartMap.smart_interp_flat_map] in e.
  repeat match eval cbv delta [e] in e with
         | context[Z.eqb ?x ?y]
           => set (k := Z.eqb x y) in (value of e);
                vm_compute in k; subst k
         end.
  cbv beta iota in e.
  Timeout 5 vm_compute in e.
                         subst
  unfold CPSUtil.fold_right_cps2_specialized_step at 1 in (value of e); cbn [fst snd] in e.
  cbn [PairZOrExpr exprOfZOrExpr OpZOrExpr interp_op curry2] in e.
  cbv [SmartMap.SmartVarfMap SmartMap.SmartPairf] in e.
  cbn [PairZOrExpr exprOfZOrExpr OpZOrExpr interp_op curry2 SmartMap.smart_interp_flat_map] in e.
  unfold CPSUtil.fold_right_cps2_specialized_step at 1 in (value of e); cbn [fst snd] in e.
  cbn [PairZOrExpr exprOfZOrExpr OpZOrExpr interp_op curry2] in e.
  cbv [SmartMap.SmartVarfMap SmartMap.SmartPairf] in e.
  cbn [PairZOrExpr exprOfZOrExpr OpZOrExpr interp_op curry2 SmartMap.smart_interp_flat_map] in e.
  cbn [PairZOrExpr exprOfZOrExpr OpZOrExpr interp_op curry2] in e.

  cbv [inline_const_and_opf Compilers.InlineConstAndOpByRewrite.Rewrite.inline_const_and_opf InlineConstAndOpByRewrite.Rewrite.Const InlineConstAndOpByRewrite.Rewrite.invert_ConstUnit] in e.
  Notation rewf := (Rewriter.rewrite_opf _).
  Notation rewf' := (InlineConstAndOpByRewrite.Rewrite.rewrite_for_const_and_op _ _ _ _ _ ).
  unfold CPSUtil.fold_right_cps2_specialized_step at 1 in (value of e); cbn [fst snd] in e.
  cbn [SmartMap.smart_interp_flat_map fst snd inline_const_and_opf] in e.
  cbn [InlineConstAndOpByRewrite.Rewrite.inline_const_and_op_genf] in e.
  cbv [InlineConstAndOpByRewrite.Rewrite.inline_const_and_op_genf] in e.
  cbv [InlineConstAndOpByRewrite.Rewrite.rewrite_for_const_and_op] in e.
  cbv [InlineConstAndOpByRewrite.Rewrite.rewrite_for_const_and_op] in e.
  cbn [Rewriter.rewrite_opf] in e.
  About InlineConstAndOpByRewrite.Rewrite.rewrite_for_const_and_op.
  Arguments InlineConstAndOpByRewrite.Rewrite.rewrite_for_const_and_op _ _ _ _ _ _ _ _ _ !_ _ / .
  cbv [inline_const_and_opf Compilers.InlineConstAndOpByRewrite.Rewrite.inline_const_and_op_genf Compilers.InlineConstAndOpByRewrite.Rewrite.inline_const_and_opf InlineConstAndOpByRewrite.Rewrite.Const] in e;
    cbn [Rewriter.rewrite_opf InlineConstAndOpByRewrite.Rewrite.rewrite_for_const_and_op] in e.
  cbv [linearizef] in e; cbn [linearizef_gen under_letsf] in e.
  do 2 (cbv [InlineConstAndOpByRewrite.Rewrite.rewrite_for_const_and_op SmartMap.SmartPairf SmartMap.SmartVarfMap curry2 InlineConstAndOpByRewrite.Rewrite.invert_ConstUnit] in e;
        cbn [id
               InlineConstAndOpByRewrite.Rewrite.rewrite_for_const_and_op SmartMap.SmartPairf SmartMap.SmartVarfMap curry2 InlineConstAndOpByRewrite.Rewrite.invert_ConstUnit
               ExprInversion.invert_PairsConst SmartMap.smart_interp_flat_map interp_op InlineConstAndOpByRewrite.Rewrite.invert_ConstUnit'] in e).

  cbv [] in e.
  cbn [] in e.
  cbn [interp_op] in e.
  cbv [curry2] in e.
  cbn [InlineConstAndOpByRewrite.Rewrite.rewrite_for_const_and_op] in e.
  unfold CPSUtil.fold_right_cps2_specialized_step at 1 in (value of e); cbn [fst snd] in e.
  unfold CPSUtil.fold_right_cps2_specialized_step at 1 in (value of e); cbn [fst snd] in e.
  unfold CPSUtil.fold_right_cps2_specialized_step at 1 in (value of e); cbn [fst snd] in e.
  unfold CPSUtil.fold_right_cps2_specialized_step at 1 in (value of e).
  cbn [fst snd] in e.
  cbv beta in e.
  cbv iota in e.
  cbv [CPSUtil.fold_right_cps2_specialized] in e.
  cbv [CPSUtil.to_list_cps] in e.
  cbn [] in e.
  cbn [interp_flat_type Syntax.tuple'] in e.
  cbv [SmartMap.SmartVarfMap] in e.
  cbn [SmartMap.smart_interp_flat_map] in e.
  cbv [InlineConstAndOp] in e.
  Timeout 3 vm_compute in e.
  cbn [SmartMap.SmartVarfMap] in e.
Timeout 3 Eval vm_compute in compiled_add.
Definition compiled_add_sig (weight : nat -> Z) (n : nat)
  : option
      { add : Z.Syntax.Expr (Syntax.Prod (Syntax.tuple (Tbase Z.Syntax.TZ) n)
                                         (Syntax.tuple (Tbase Z.Syntax.TZ) n)
                             -> Syntax.tuple (Tbase Z.Syntax.TZ) n)
      | (forall v, Z.Syntax.Interp add v = flat_interp_untuple (T:=Tbase Z.Syntax.TZ) (@Core.B.Positional.add_cps weight n (flat_interp_tuple (fst v)) (flat_interp_tuple (snd v)) _ id))
        /\ Wf add }.
Proof.
  let t := compile (fun var n f weight xy => @Core.B.Positional.add_cps weight n (fst xy) (snd xy) (@exprZ (fun t => @exprZ var (Tbase t)) (tuple tZ n)) f) in
  let t := post_compile (fun var xy => t var n weight xy) in
  idtac t;
  let T := type of t in pose T.

Section gen.
  Context (interp_base_type : base_type -> Set).

  Fixpoint interp_type_gen (t : type) : Set :=
    match t with
    | Unit => unit
    | Tbase T => interp_base_type T
    | Prod A B => interp_type_gen A * interp_type_gen B
    end.

  Fixpoint to_interp_flat_type {t} : interp_type_gen t -> interp_flat_type interp_base_type t
    := match t with
       | Tbase T => fun x => x
       | Unit => fun x => x
       | Prod A B => fun ab : interp_type_gen A * interp_type_gen B
                     => (to_interp_flat_type (fst ab), to_interp_flat_type (snd ab))
       end.
  Fixpoint of_interp_flat_type {t} : interp_flat_type interp_base_type t -> interp_type_gen t
    := match t with
       | Tbase T => fun x => x
       | Unit => fun x => x
       | Prod A B => fun ab : interp_flat_type _ A * interp_flat_type _ B
                     => (of_interp_flat_type (fst ab), of_interp_flat_type (snd ab))
       end.
End gen.
Arguments to_interp_flat_type {_ t} _ : assert.
Arguments of_interp_flat_type {_ t} _ : assert.
Section map.
  Context {var1 var2 : base_type -> Set}
          (f : forall t, var1 t -> var2 t).
  Fixpoint map_interp_type_gen {t : type} : interp_type_gen var1 t -> interp_type_gen var2 t
    := match t with
       | Unit => fun x => x
       | Tbase T => f _
       | Prod A B => fun ab : interp_type_gen _ A * interp_type_gen _ B
                     => (map_interp_type_gen (fst ab), map_interp_type_gen (snd ab))
       end.
End map.
Notation interp_type := (interp_type_gen interp_base_type).
Notation tZ := (Tbase TZ).
Notation tBool := (Tbase Tbool).

Inductive op : type -> type -> Set :=
| AddGetCarry : op (tuple tZ 3) (tuple tZ 2)
| MulSplitAtBitwidth : op (tuple tZ 3) (tuple tZ 2)
| Zselect : op (tuple tZ 3) (tuple tZ 1)
| Zmul    : op (tuple tZ 2) (tuple tZ 1)
| Zadd    : op (tuple tZ 2) (tuple tZ 1)
| Zopp    : op (tuple tZ 1) (tuple tZ 1)
| Zshiftr : op (tuple tZ 2) (tuple tZ 1)
| Zshiftl : op (tuple tZ 2) (tuple tZ 1)
| Zland   : op (tuple tZ 2) (tuple tZ 1)
| Zlor    : op (tuple tZ 2) (tuple tZ 1)
| Zmodulo : op (tuple tZ 2) (tuple tZ 1)
| Zdiv    : op (tuple tZ 2) (tuple tZ 1)
| Zlog2   : op (tuple tZ 1) (tuple tZ 1)
| Zpow    : op (tuple tZ 2) (tuple tZ 1)
| Zones   : op (tuple tZ 1) (tuple tZ 1)
| Zeqb    : op (tuple tZ 2) (tuple tBool 1)
| ConstZ (v : BinNums.Z) : op (tuple tZ 0) (tuple tZ 1)
| ConstBool (v : bool) : op (tuple tZ 0) (tuple tBool 1)
| BoolCase {T} : op (Prod (Prod tBool T) T) T.

Definition Const {t} : interp_base_type t -> op Unit (Tbase t)
  := match t with
     | TZ => ConstZ
     | Tbool => ConstBool
     end.

Local Notation eta x := (fst x, snd x).
Local Notation eta3 x := (eta (fst x), snd x).
Local Notation eta4 x := (eta3 (fst x), snd x).


Notation interp_op_body opv :=
  (match opv with
   | AddGetCarry => curry3 Z.add_get_carry
   | MulSplitAtBitwidth => curry3 Z.mul_split_at_bitwidth
   | Zselect => curry3 Z.zselect
   | Zmul => curry2 Z.mul
   | Zadd => curry2 Z.add
   | Zopp => Z.opp
   | Zshiftr => curry2 Z.shiftr
   | Zshiftl => curry2 Z.shiftl
   | Zland => curry2 Z.land
   | Zlor => curry2 Z.lor
   | Zmodulo => curry2 Z.modulo
   | Zdiv => curry2 Z.div
   | Zlog2 => Z.log2
   | Zpow => curry2 Z.pow
   | Zones => Z.ones
   | Zeqb => curry2 Z.eqb
   | ConstZ v => fun _ => v
   | ConstBool v => fun _ => v
   | BoolCase T => fun '(b, t, f) => if b then t else f
   end).

Definition interp_op' {s d} (opv : op s d) : interp_type s -> interp_type d
  := interp_op_body opv.

Inductive exprZ {var : base_type -> Set} : type -> Set :=
| Op {src dst} (opv : op src dst) (args : exprZ src) : exprZ dst
| TT : exprZ Unit
| Pair {tx ty} (ex : exprZ tx) (ey : exprZ ty) : exprZ (Prod tx ty)
| Var {t} (v : var t) : exprZ (Tbase t)
| LetIn {tx tC} (ex : exprZ tx) (eC : interp_type_gen var tx -> exprZ tC)
  : exprZ tC.

Fixpoint of_tuple' {var T n} : Tuple.tuple' (@exprZ var T) n -> @exprZ var (tuple' T n)
  := match n with
     | 0 => fun x => x
     | S n' => fun xy : (Tuple.tuple' (exprZ _) _ * exprZ _)%type
               => Pair (of_tuple' (fst xy)) (snd xy)
     end.
Definition of_tuple {var T n} : Tuple.tuple (@exprZ var T) n -> @exprZ var (tuple T n)
  := match n with
     | 0 => fun x => TT
     | S n' => of_tuple'
     end.

Fixpoint compile {var T} (e : @exprZ var T)
  : @Syntax.exprf base_type op var T
  := match e with
     | Op src dst opv args
       => Syntax.Op opv (@compile _ _ args)
     | TT => Syntax.TT
     | Pair tx ty ex ey => Syntax.Pair (@compile _ _ ex) (@compile _ _ ey)
     | Var t v => Syntax.Var v
     | LetIn tx tC ex eC => Syntax.LetIn (@compile _ _ ex) (fun v => @compile _ _ (eC (of_interp_flat_type v)))
     end.

Scheme Equality for base_type.
Print Core.B.Positional.add_cps.

Local Notation PContext var := (PositiveContext.PositiveContext _ var _ internal_base_type_dec_bl0).
Definition interp_op {s d} (opv : op s d) : interp_flat_type interp_base_type s -> interp_flat_type interp_base_type d
  := interp_op_body opv.
Print Core.B.Positional.add_cps.

Definition compiled_add_sig (weight : nat -> Z) (n : nat)
  : option
      { add : Syntax.Expr (Syntax.Prod (Syntax.tuple (Tbase Syntax.TZ) n)
                                       (Syntax.tuple (Tbase Syntax.TZ) n)
                           -> Syntax.tuple (Tbase Syntax.TZ) n)
      | (forall v, Syntax.Interp add v = flat_interp_untuple (T:=Tbase Syntax.TZ) (@Core.B.Positional.add_cps weight n (flat_interp_tuple (fst v)) (flat_interp_tuple (snd v)) _ id))
        /\ Wf add }.
Proof.
  let t := compile (fun var n f weight xy => @Core.B.Positional.add_cps weight n (fst xy) (snd xy) (@exprZ (fun t => @exprZ var (Tbase t)) (tuple tZ n)) f) in
  let t := post_compile (fun var xy => t var n weight xy) in
  let T := type of t in pose T.
*)
