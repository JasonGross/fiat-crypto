Require Import Crypto.Arithmetic.CoreUnfolder.
Require Import Crypto.Arithmetic.Saturated.CoreUnfolder.
Require Import Crypto.Arithmetic.Saturated.WrappersUnfolder.
Require Import Crypto.Arithmetic.Saturated.Freeze.

(**
<<
#!/bin/bash
for i in freeze freeze_cps; do
    echo "Definition ${i}_sig := parameterize_sig (@Freeze.${i}).";
    echo "Definition ${i} := parameterize_from_sig ${i}_sig.";
    echo "Definition ${i}_eq := parameterize_eq ${i} ${i}_sig.";
    echo "Hint Unfold ${i} : basesystem_partial_evaluation_unfolder.";
    echo "Hint Rewrite <- ${i}_eq : pattern_runtime."; echo "";
done
>> *)
Definition freeze_cps_sig := parameterize_sig (@Freeze.freeze_cps).
Definition freeze_cps := parameterize_from_sig freeze_cps_sig.
Definition freeze_cps_eq := parameterize_eq freeze_cps freeze_cps_sig.
Hint Unfold freeze_cps : basesystem_partial_evaluation_unfolder.
Hint Rewrite <- freeze_cps_eq : pattern_runtime.

Definition freeze_sig := parameterize_sig (@Freeze.freeze).
Definition freeze := parameterize_from_sig freeze_sig.
Definition freeze_eq := parameterize_eq freeze freeze_sig.
Hint Unfold freeze : basesystem_partial_evaluation_unfolder.
Hint Rewrite <- freeze_eq : pattern_runtime.

Import BinNums BinInt ZArith LetIn.


Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Syntax.
Inductive base_type : Set := TZ | Tbool.
Notation type := (flat_type base_type).

Definition interp_base_type (t : base_type) : Set
  := match t with
     | TZ => BinNums.Z
     | Tbool => bool
     end.
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
| BoolCase {T} : op (Prod (Prod tBool T) T) T.


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
Fixpoint strip_expr {var T} (e : @exprZ (fun t => @exprZ var (Tbase t)) T) : @exprZ var T
  := match e with
     | Op src dst opv args
       => Op opv (strip_expr args)
     | TT => TT
     | Pair tx ty ex ey
       => Pair (strip_expr ex) (strip_expr ey)
     | Var t v
       => v
     | LetIn tx tC ex eC
       => LetIn (strip_expr ex) (fun v => strip_expr (eC (map_interp_type_gen (@Var _) v)))
     end.
Import Arithmetic.Core ZUtil.Definitions ZUtil.CPS Util.IdfunWithAlt.

Local Notation lift1 f :=
  (fun x => Op f x).
Local Notation lift2 f :=
  (fun x y => Op f (Pair x y)).
Local Notation lift3 f :=
  (fun x y z => Op f (Pair (Pair x y) z)).

Ltac compile t :=
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
           fun (var : base_type -> Set) (n : nat)
           => ltac:(
                let t := (eval cbv beta in (t var n)) in
                let T := constr:(@exprZ (fun ty => @exprZ var (Tbase ty)) (tuple tZ n)) in
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
                exact t)) in
  let t := (eval cbv beta iota in
               (fun var n weight mask m p
                => t var n (@exprZ var tZ)
                     (fun v' f => LetIn (Var v') f)
                     (fun v' f => LetIn (Pair (Var (fst v')) (Var (snd v'))) f)
                     (fun x y z f => LetIn (var:=fun ty => @exprZ var (Tbase ty)) (Op AddGetCarry (Pair (Pair (Var x) (Var y)) (Var z))) f)
                     (fun x y z f => LetIn (var:=fun ty => @exprZ var (Tbase ty)) (Op MulSplitAtBitwidth (Pair (Pair (Var x) (Var y)) (Var z))) f)
                     (fun x y f => Op BoolCase (Pair (Pair (Op Zeqb (Pair (Var x) (Var y))) (f true)) (f false)))
                     (lift3 Zselect)
                     (lift2 Zmul) (lift2 Zadd) (lift1 Zopp) (lift2 Zshiftr) (lift2 Zland) (lift2 Zlor)
                     (lift2 Zmul) (lift2 Zadd) (lift1 Zopp) (lift2 Zshiftr) (lift2 Zshiftl) (lift2 Zland) (lift2 Zlor)
                     (lift2 Zmodulo) (lift2 Zdiv) (lift1 Zlog2) (lift2 Zpow) (lift1 Zones)
                     (Op (ConstZ 2%Z) TT) (Op (ConstZ 1%Z) TT) (Op (ConstZ 0%Z) TT)
                     (fun ts => of_tuple (Tuple.map Var ts))
                     (fun n => Op (ConstZ (weight n)) TT)
                     (Op (ConstZ mask) TT)
                     (Tuple.map (fun v => Op (ConstZ v) TT) m)
                     (Tuple.map (fun v => Op (ConstZ v) TT) p)
           )) in
  t.
Print Freeze.freeze_cps.
Require Import Crypto.Compilers.Tuple.
Require Import Crypto.Compilers.Wf.
Require Crypto.Compilers.Inline.
Require Crypto.Compilers.Named.Context.
Require Crypto.Compilers.Named.Syntax.
Require Crypto.Compilers.Named.InterpretToPHOAS.
Require Crypto.Compilers.Named.Compile.
Require Crypto.Compilers.Named.PositiveContext.
Require Crypto.Compilers.Named.PositiveContext.Defaults.

Scheme Equality for base_type.

Local Notation PContext var := (PositiveContext.PositiveContext _ var _ internal_base_type_dec_bl0).
Local Definition failb : forall var t, @Syntax.exprf base_type op var (Tbase t)
  := fun var t
     => match t with
        | TZ => Syntax.Op (ConstZ 0%Z) Syntax.TT
        | Tbool => Syntax.Op Zeqb (Syntax.Pair (Syntax.Op (ConstZ 0%Z) Syntax.TT) (Syntax.Op (ConstZ 0%Z) Syntax.TT))
        end.

Section postprocess.
  Import Compilers.Syntax Inline.

  Fixpoint postprocess {var t} (e : @exprf base_type op var t)
    : Inline.inline_directive (var:=var) (op:=op) t.
    refine match e with
           | TT => inline (t:=Unit) tt
           | Var t v => inline (t:=Tbase _) (Var v)
           | Op t1 tR opc args
             => match opc in op src dst return exprf _ _ src -> _ with
                | AddGetCarry => _
                | MulSplitAtBitwidth => _
                | Zselect => _
                | Zmul => _
                | Zadd => _
                | Zopp => _
                | Zshiftr => _
                | Zshiftl => _
                | Zland => _
                | Zlor => _
                | Zmodulo => _
                | Zdiv => _
                | Zlog2 => _
                | Zpow => _
                | Zones => _
                | Zeqb => _
                | ConstZ v => _
                | BoolCase T => _
                end args
           | LetIn _ _ _ _ as e
             => default_inline e
           | Pair tx ex ty ey as e
             => match @postprocess _ _ ex, @postprocess _ _ ey with
                | default_inline _ ex, default_inline _ ey
                  => default_inline e
                | inline _ ex, inline _ ey => inline _
                | no_inline _ ex, no_inline _ ey => _
                | _, _ => _
                end
           end;
      simpl.
  Abort.
End postprocess.

Definition post_compile {n} (t : forall var : base_type -> Set, @exprZ (fun t => @exprZ var (Tbase t)) (tZ ^ n))
  := let t := (fun var => Syntax.Abs (src:=Unit) (fun _ => compile (strip_expr (t var)))) in
     let t := Named.Compile.compile
                (t (fun _ => positive))
                (Defaults.default_names_for (fun _ => tt) (t (fun _ => unit))) in
     let t := option_map
                (fun e
                 => let e := InterpretToPHOAS.Named.InterpToPHOAS
                               (base_type_code:=base_type) (Context:=fun var => PContext var) failb e in
                    (*let e := Inline.InlineConstGen
                                    e in*)
                    e
                )
                t in
     t.

Ltac post_compile t :=
  let t := (eval cbv [post_compile] in (post_compile t)) in
  let t := (eval cbn [domain codomain] in t) in
  t.

Definition compiled_freeze_sig (weight : nat -> Z) (n : nat) (mask : Z) (m p : Tuple.tuple Z n)
  : option
      { freeze : Syntax.Expr (Syntax.Unit -> Syntax.tuple (Tbase Syntax.TZ) n)
      | (forall v : unit, Syntax.Interp freeze v = flat_interp_untuple (T:=Tbase Syntax.TZ) (@Freeze.freeze weight n mask m p))
        /\ Wf freeze }.
Proof.
  let t := compile (fun var n f weight mask m p => @Freeze.freeze_cps weight n mask m p (@exprZ (fun t => @exprZ var (Tbase t)) (tuple tZ n)) f) in
  let t := post_compile (fun var => t var n weight mask m p) in
  let T := type of t in pose T.

  pose (@Inline.InlineConst).
                          cbn
  pose t.
  Check .
  refine (match t as t' return t = t' -> _ with
          | Some v => fun pf => Some (exist _ v _)
          | None => fun _ => None
          end eq_refl).
  eexists.
  cbv [Freeze.freeze].
  Set Printing Implicit.
  pose t.
  cbn [domain codomain] in *.
  ( e'')

Goal (base_type -> Set) -> True.
  intro var.
  Print freeze_cps.
  pose  as e.
  let t := (eval cbv delta [e] in e) in
  clear e;
  let t := compile t in
  pose t.
  (* (fun t => of_tuple (Tuple.map ConstZ t))) as e. *)
  Set Printing Depth 100000.
  repeat autounfold with basesystem_partial_evaluation_unfolder in e.
  let t := (eval cbv [proj1_sig e] in e) in
  clear e;
    pose t as e.
   let v := (eval cbv delta [e] in e) in
   clear e;
    pose t as e.

  Arguments LetIn.Let_In : clear implicits.
  Arguments Z.eqb_cps : clear implicits.
  Arguments Z.add_get_carry_cps : clear implicits.
  let t := (eval pattern
                 (@Z.add_get_carry_cps (exprZ (tuple tZ n))), @Z.mul_split_at_bitwidth_cps,
            (@Z.eq_dec_cps), (@Z.eqb_cps)
            ,

            (@id_with_alt Z),
            @Z.add_get_carry, @Z.zselect, @Z.mul_split_at_bitwidth,
            Z.eq_dec, Z.eqb,
            (@ModularArithmetic.F.to_Z), (@ModularArithmetic.F.of_Z),
            2%Z, 1%Z, 0%Z
             in t) in
                              exact t)) in
    pose t as e.
  let t := match t with ?t
                         _
                         _ _
                         _ _
                         _ _ _ _ _ _
                         _
                         _ _ _
                         _ _ _ _ _ _ _
                         _ _ _ _ _
                         _ _
                         _ _
                         _ _ _ => t end in
  let t := (eval pattern Z, (@Let_In), (@id_with_alt) in t) in
  let t := match t with ?t _ _ _ => t end in
  t.

  let t := pattern_strip_full t in
  pose t as e'.
  clear e.
  let v := (eval cbv delta [e'] in e') in
  clear e';
    let t := (eval cbv beta in
                 (v (@exprZ var TZ) (@LetIn.Let_In))) in
    let t := match t with fun _ => ?t => t end in (* strip generic id with alt *)
    let t := (eval cbv beta in
                 (t (fun v' f => @LetIn var (Tbase TZ) (Tbase TZ) v' (fun v' => f (Var v'))))) in
    pose t as e.
    cbv beta

  Arguments LetIn.Let_In : clear implicits.
  Arguments CPS.Z.eqb_cps : clear implicits.
