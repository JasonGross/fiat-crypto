Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Export Crypto.Specific.GF25519.
Require Import Crypto.Specific.GF25519BoundedCommon.
Require Import Crypto.Reflection.Reify.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.MapInterp.
Require Import Crypto.Reflection.Z.Interpretations.
Require Crypto.Reflection.Z.Interpretations.Relations.
Require Import Crypto.Reflection.Z.Interpretations.RelationsCombinations.
Require Import Crypto.Reflection.Z.Reify.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Specific.GF25519Reflective.Common.
Require Import Crypto.Specific.GF25519Reflective.Reified.
Require Import Bedrock.Word Crypto.Util.WordUtil.
Require Import Coq.Lists.List Crypto.Util.ListUtil.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Algebra.
Import ListNotations.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Local Open Scope Z.

Definition radd : ExprBinOp := Eval vm_compute in rcarry_addW.
Definition rsub : ExprBinOp := Eval vm_compute in rcarry_subW.
Definition rmul : ExprBinOp := Eval vm_compute in rmulW.
Definition ropp : ExprUnOp := Eval vm_compute in rcarry_oppW.
Definition rfreeze : ExprUnOp := Eval vm_compute in rfreezeW.
Definition rge_modulus : ExprUnOpFEToZ := Eval vm_compute in rge_modulusW.
Definition rpack : ExprUnOpFEToWire := Eval vm_compute in rpackW.
Definition runpack : ExprUnOpWireToFE := Eval vm_compute in runpackW.

Definition rword64ize {t} (x : Expr t) : Expr t
  := MapInterp (fun t => match t with TZ => word64ize end) x.

Declare Reduction asm_interp
  := cbv beta iota delta
         [id
            interp_bexpr interp_uexpr interp_uexpr_FEToWire interp_uexpr_FEToZ interp_uexpr_WireToFE
            radd rsub rmul ropp rfreeze rge_modulus rpack runpack
            curry_binop_fe25519W curry_unop_fe25519W curry_unop_wire_digitsW
            Word64.interp_op Word64.interp_base_type
            Z.interp_op Z.interp_base_type
            Z.Syntax.interp_op Z.Syntax.interp_base_type
            mapf_interp_flat_type map_interp Word64.interp_base_type MapInterp mapf_interp word64ize rword64ize
            Interp interp interp_flat_type interpf interp_flat_type fst snd].
Ltac asm_interp
  := cbv beta iota delta
         [id
            interp_bexpr interp_uexpr interp_uexpr_FEToWire interp_uexpr_FEToZ interp_uexpr_WireToFE
            radd rsub rmul ropp rfreeze rge_modulus rpack runpack
            curry_binop_fe25519W curry_unop_fe25519W curry_unop_wire_digitsW
            Word64.interp_op Word64.interp_base_type
            Z.interp_op Z.interp_base_type
            Z.Syntax.interp_op Z.Syntax.interp_base_type
            mapf_interp_flat_type map_interp Word64.interp_base_type MapInterp mapf_interp word64ize rword64ize
            Interp interp interp_flat_type interpf interp_flat_type fst snd].


Definition interp_radd : Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W
  := Eval asm_interp in interp_bexpr (rword64ize radd).
(*Print interp_radd.*)
Definition interp_radd_correct : interp_radd = interp_bexpr radd := eq_refl.
Definition interp_rsub : Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W
  := Eval asm_interp in interp_bexpr (rword64ize rsub).
(*Print interp_rsub.*)
Definition interp_rsub_correct : interp_rsub = interp_bexpr rsub := eq_refl.
Definition interp_rmul : Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W
  := Eval asm_interp in interp_bexpr (rword64ize rmul).
(*Print interp_rmul.*)
Definition interp_rmul_correct : interp_rmul = interp_bexpr rmul := eq_refl.
Definition interp_ropp : Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W
  := Eval asm_interp in interp_uexpr (rword64ize ropp).
(*Print interp_ropp.*)
Definition interp_ropp_correct : interp_ropp = interp_uexpr ropp := eq_refl.
Definition interp_rfreeze : Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W
  := Eval asm_interp in interp_uexpr (rword64ize rfreeze).
(*Print interp_rfreeze.*)
Definition interp_rfreeze_correct : interp_rfreeze = interp_uexpr rfreeze := eq_refl.

Definition interp_rge_modulus : Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.word64
  := Eval asm_interp in interp_uexpr_FEToZ (rword64ize rge_modulus).
Definition interp_rge_modulus_correct : interp_rge_modulus = interp_uexpr_FEToZ rge_modulus := eq_refl.

Definition interp_rpack : Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.wire_digitsW
  := Eval asm_interp in interp_uexpr_FEToWire (rword64ize rpack).
Definition interp_rpack_correct : interp_rpack = interp_uexpr_FEToWire rpack := eq_refl.

Definition interp_runpack : Specific.GF25519BoundedCommon.wire_digitsW -> Specific.GF25519BoundedCommon.fe25519W
  := Eval asm_interp in interp_uexpr_WireToFE (rword64ize runpack).
Definition interp_runpack_correct : interp_runpack = interp_uexpr_WireToFE runpack := eq_refl.

Local Notation binop_correct_and_bounded rop op
  := (ibinop_correct_and_bounded (interp_bexpr rop) op) (only parsing).
Local Notation unop_correct_and_bounded rop op
  := (iunop_correct_and_bounded (interp_uexpr rop) op) (only parsing).
Local Notation unop_FEToZ_correct rop op
  := (iunop_FEToZ_correct (interp_uexpr_FEToZ rop) op) (only parsing).
Local Notation unop_FEToWire_correct_and_bounded rop op
  := (iunop_FEToWire_correct_and_bounded (interp_uexpr_FEToWire rop) op) (only parsing).
Local Notation unop_WireToFE_correct_and_bounded rop op
  := (iunop_WireToFE_correct_and_bounded (interp_uexpr_WireToFE rop) op) (only parsing).

Local Ltac start_correct_and_bounded_t op op_expr lem :=
  intros; hnf in *; destruct_head' prod; simpl in * |- ;
  repeat match goal with H : is_bounded _ = true |- _ => unfold_is_bounded_in H end;
  repeat match goal with H : wire_digits_is_bounded _ = true |- _ => unfold_is_bounded_in H end;
  change op with op_expr;
  rewrite <- lem.

Local Opaque Interp.
Lemma radd_correct_and_bounded : binop_correct_and_bounded radd carry_add.
Proof.
  intros; hnf in *; destruct_head' prod; simpl in * |- .
  repeat match goal with H : is_bounded _ = true |- _ => unfold_is_bounded_in H end.
  change radd with (MapInterp (fun _ x => x) rcarry_addW).
  pose proof rcarry_addW_correct_and_bounded_gen as Hbounds.
  cbv zeta in Hbounds.
  cbv [interp_bexpr curry_binop_fe25519W] in *.
  pose proof (proj2_sig rcarry_addZ_sig) as Heq.
  cbv beta iota delta [interp_type_gen_rel_pointwise uncurry_binop_fe25519 ExprBinOpT] in *.
  simpl @fe25519WToZ.
  rewrite <- Heq; clear Heq.
  destruct Hbounds as [Heq Hbounds].
  change interp_op with (@Z.interp_op) in *.
  change interp_base_type with (@Z.interp_base_type) in *.
  cbv beta iota delta [interp_type_gen_rel_pointwise uncurry_binop_fe25519 ExprBinOpT] in *.
  rewrite <- Heq; clear Heq.
  generalize dependent ((Interp (@Word64.interp_op)
                                (MapInterp (fun (t : base_type) (x : Word64.interp_base_type t) => x) rcarry_addW))); intro rcarry_addWI; intros.
  generalize dependent (Interp (@Z.interp_op) (MapInterp Word64.to_Z rcarry_addW));
    intro rcarry_addZI; intros.
  destruct Hbounds as [Hbounds0 [Hbounds1 Hbounds2] ].
  pose proof (fun pf => Relations.uncurry_interp_type_rel_pointwise2_proj_from_option2 Word64.to_Z pf Hbounds2 Hbounds0) as Hbounds_left.
  pose proof (fun pf => Relations.uncurry_interp_type_rel_pointwise2_proj1_from_option2 Relations.related_word64_boundsi' pf Hbounds1 Hbounds2) as Hbounds_right.
  specialize_by repeat first [ progress intros
                             | reflexivity
                             | assumption
                             | progress destruct_head' base_type
                             | progress destruct_head' BoundedWord64.BoundedWord
                             | progress destruct_head' and
                             | progress repeat apply conj ].
  destruct_head' and.
  Z.ltb_to_lt.
  Set Printing Coercions.
  Ltac args_to_bounded f so_far :=
    lazymatch f with
    | ?f' ?w
      => lazymatch goal with
         | [ H0 : ?l <= word64ToZ w, H1 : word64ToZ w <= ?u |- _ ]
           => let bounds := constr:(fun p1 p2 =>
                                      {| BoundedWord64.lower := l ; BoundedWord64.value := w ; BoundedWord64.upper := u ;
                                         BoundedWord64.in_bounds := (conj p1 (conj (conj H0 H1) p2)) |}) in
              let bounds := (eval cbv beta in (bounds (fun x => match x with eq_refl => I end) eq_refl)) in
              let so_far := lazymatch so_far with
                            | @None => bounds
                            | ?rest => constr:((bounds, rest))
                            end in
              args_to_bounded f' so_far
         end
    | _ => so_far
    end.
  lazymatch goal with
  | [ |- context[fe25519WToZ ?x] ]
    => let v := args_to_bounded x (@None) in pose v as args
  end.
  move args at top.
  specialize (Hbounds_left args I).
  specialize (Hbounds_right args I).
  lazymatch type of Hbounds_right with
  | match ?e with _ => _ end => let k := fresh in set (k := e) in *; vm_compute in k; subst k
  end.
  hnf in Hbounds_left, Hbounds_right.
  move Hbounds_left at bottom.
  cbv [Relations.proj_eq_rel interp_flat_type_rel_pointwise2 SmartVarfMap interp_flat_type smart_interp_flat_map Application.all_binders_for fst snd args BoundedWord64.to_word64' BoundedWord64.boundedWordToWord64 BoundedWord64.value Application.ApplyInterpedAll Application.fst_binder Application.snd_binder interp_flat_type_rel_pointwise2_gen_Prop Relations.related_word64_boundsi' Relations.related'_word64_bounds ZBounds.upper ZBounds.lower Application.remove_all_binders Word64.to_Z (*args*)] in Hbounds_left, Hbounds_right.
    change Word64.word64ToZ with word64ToZ in *.
    rewrite <- Hbounds_left; clear Hbounds_left.
    destruct_head' and.
    match goal with
    | [ |- fe25519WToZ ?x = _ /\ _ ]
      => destruct x; destruct_head_hnf' prod
    end.
    Ltac unfold_is_bounded :=
  unfold is_bounded, wire_digits_is_bounded, is_bounded_gen, fe25519WToZ, wire_digitsWToZ;
  cbv [to_list length bounds wire_digit_bounds from_list from_list' map2 on_tuple2 to_list' ListUtil.map2 List.map fold_right List.rev List.app length_fe25519 List.length wire_widths];
  rewrite ?Bool.andb_true_iff.
      unfold_is_bounded.
      repeat apply conj; Z.ltb_to_lt; try omega; try reflexivity. }

      cbv [is_bounded fe25519WToZ is_bounded_gen Tuple.map2 Tuple.on_tuple2 Tuple.to_list Tuple.to_list' length_fe25519 List.rev List.app ListUtil.map2 Tuple.from_list Tuple.from_list' bounds].
      SearchAbout is_bounded
      match goal with
      | [ H : ?x = true |- context[?x] ] => rewrite H
      end.
    match k' as b return match b with Some _ => _ | None => True end with
    | Some f' =>
    assert (fold_right andb true (
    match type of Hbounds1 with
    | ?x = ?y => set (HL := x) in Hbounds1; set (HR := y) in Hbounds1
    end.
    move HL at bottom.
    move HL at bottom.
    vm_compute in HL.
    move HR at bottom.


    Print is_bounded.
    Print is_bounded_gen.
    Print SmartVarfMap.
    Print fe25519WToZ.
    cbv [
    compute in v0.
    compute in v1.
    cbv [Application.ApplyInterpedAll] in Hbounds_left.
  generalize dependent ( LiftOption.of'
                           (Application.ApplyInterpedAll (Interp (@BoundedWord64.interp_op) (MapInterp BoundedWord64.of_word64 rcarry_addW))
                                                                             (LiftOption.to' (Some args)))).

  set (k := SmartVarfMap (t:=_) BoundedWord64.to_word64') in *.
  Timeout 2 hnf in Hbounds0.
  Timeout 2 hnf in Hbounds1.
  Timeout 2 hnf in Hbounds2.
  specialize (Hbounds1 args).
  Ltac specialize_by_A
  cbv [Application.ApplyInterpedAll] in *.
  (*** HERE *)
  rewrite !Relations.uncurry_interp_type_rel_pointwise2 in Hbounds.
  cbv [Relations.interp_type_rel_pointwise2_uncurried] in *.
  simpl @interp_flat_type in *.
  About Relations.related_Zi.
  Definition related_word_Zi (t : base_type) : Word64.interp_base_type t -> Z.interp_base_type t -> Prop
    := match t with
       | TZ => fun x y => Word64.word64ToZ x = y
       end.
  assert (Hboundseq : interp_type_rel_pointwise2 related_word_Zi
              rcarry_addWI rcarry_addZI) by admit.
  Definition related_word_boundsi (t : base_type) : Word64.interp_base_type t -> ZBounds.interp_base_type t -> Prop
    := match t with
       | TZ => fun value b
               => match b with
                  | Some b
                    => let (lower, upper) := b in
                       (0 <= lower /\ lower <= Word64.word64ToZ value <= upper /\ Z.log2 upper < Z.of_nat Word64.bit_width)%Z
                  | None => True
                  end
       end.
  assert (Hboundsb : interp_type_rel_pointwise2 related_word_boundsi
                                                rcarry_addWI (Interp (@ZBounds.interp_op) (MapInterp ZBounds.of_word64 rcarry_addW))) by admit.
  clear Hbounds.
  cbv [interp_type_rel_pointwise2 interp_type_gen_rel_pointwise2  interp_type_gen_rel_pointwise2_hetero interp_type Word64.interp_base_type interp_type_gen interp_type_gen_hetero Morphisms.respectful_hetero BoundedWord64.t interp_base_type interp_flat_type_rel_pointwise2 Relations.related_word64i interp_flat_type_rel_pointwise2_gen_Prop Relations.related_Zi BoundedWord64.interp_base_type
                                  related_word_Zi                                ZBounds.t ZBounds.interp_base_type Z.interp_base_type interp_flat_type Relations.related_boundsi Relations.related_Z Relations.lift_relation Relations.related'_Z Relations.related_word64 Relations.lift_relation Relations.related'_word64 Relations.related_bounds] in *.
  move Hboundseq at bottom.
  Ltac specialize_options H :=
    let T := type of H in
    lazymatch (eval hnf in T) with
    | forall x : option ?T, _
      => let x' := fresh x in
         let x := fresh x' in
         constr:(fun x : T => ltac:(let v := specialize_options (H (Some x)) in exact v))
    | forall x : ?T, (True -> ?v = x) -> _
      => specialize_options (H _ (fun _ => eq_refl))
    | forall (x : ?T), (_ = x) -> _
      => specialize_options (H _ eq_refl)
    | forall x : ?T, _
      => let x' := fresh x in
         let x := fresh x' in
         constr:(fun x : T => ltac:(let v := specialize_options (H x) in exact v))
    | forall x : ?T, _
      => let x' := fresh x in
         let x := fresh x' in
         constr:(fun x : T => ltac:(let v := specialize_options (H x) in exact v))
    | _ => H
    end.
  repeat match goal with
         | [ H : _ /\ _ |- _ ] => destruct H
         | _ => progress cbv beta iota in *
         | [ H : forall (x : option _), _ |- _ ]
           => let v' := specialize_options H in
              pose proof v'; clear H
         | [ H : forall x y, _ = y -> _ |- _ ]
           => let H' := fresh in
              rename H into H';
                let v' := specialize_options H' in
                pose proof v' as H; clear H'
         | [ H : forall x y, (True -> _ = y) -> _ |- _ ]
           => specialize (fun x => H x _ (fun _ => eq_refl))
         end.
  specialize (Hboundseq w17 w18 w16 w15 w14 w13 w12 w11 w10 w9 w7 w8 w6 w5 w4 w3 w2 w1 w0 w).
  (* lemma that shows fieldwise eq -> eq *)
  split.
  admit.
  clear Hboundseq.
  cbv [related_word_boundsi] in *.
  cbv [is_bounded is_bounded_gen].
  Z.ltb_to_lt.
  move Hboundsb at bottom.
  Ltac specialize_more Hboundsb w :=
    specialize (fun l u => Hboundsb w (Some {| ZBounds.lower := l ; ZBounds.upper := u |})); cbv beta iota in *;
    match goal with
    | [ H0 : _ <= ?x, H1 : ?x <= _ |- _ ]
      => specialize (fun p1 p2 => Hboundsb _ _ (conj p1 (conj (conj H0 H1) p2)))
    end;
    specialize_by (vm_compute; clear; congruence).
  Ltac specialize_more_list Hboundsb t :=
    lazymatch t with
    | nil => idtac
    | cons ?x ?xs => specialize_more Hboundsb x; specialize_more_list Hboundsb xs
    end.
  specialize_more_list Hboundsb [w17;w18;w16;w15;w14;w13;w12;w11;w10;w9;w7;w8;w6;w5;w4;w3;w2;w1;w0;w].
  set (k := Interp _ _) in *.
  set (k' := k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in *.
  vm_compute in k'.
  subst k'.
  simpl @fst in *; simpl @snd in *; cbv beta iota in *.
  Locate rcarry_addW_correct_and_bounded_gen.
  (* use fieldwise in is_bounded *)
  (* fill bounds by hand first, then automate *)
  (*** HERE *)
  Set Printing Depth 1000000.
  pose (match fst ExprBinOp_bounds as x return match x with None => _ | _ => _ end with
          | Some {| ZBounds.lower := l ; ZBounds.upper := u |} => (l, u)
          | None => I
        end) as bounds17.
  compute in bounds17.
  specialize (fun x0pf => H44 {| BoundedWord64.lower := fst bounds17 ; BoundedWord64.value := w17 ; BoundedWord64.upper := snd bounds17 ; BoundedWord64.in_bounds := x0pf |}).
  Ltac specialize_via_bounded
  cbv [] in *.
  let v := specialize_options H1 in
  idtac v.

  cut (interp_type_rel_pointwise2
         Relations.related_boundsi
         (Interp (@BoundedWord64.interp_op) (MapInterp BoundedWord64.of_word64 rcarry_addW))
         (Interp (@ZBounds.interp_op) (MapInterp ZBounds.of_word64 rcarry_addW))
  pose (Application.ApplyInterped (Interp (@ZBounds.interp_op) (MapInterp ZBounds.of_word64 rcarry_addW)) ExprBinOp_bounds).
  destruct Hbounds
  Lemma interp_related_Zi interp_bounded interp_Z
    : interp_type_rel_pointwise2 Relations.related_Zi interp_bounded interp_Z
      -> _ = interp_Z
  Lemma interp_related_word64i interp_bounded interp_word
    : interp_type_rel_pointwise2 Relations.related_word64i interp_bounded interp_word
      ->
              (Interp (@BoundedWord64.interp_op) (MapInterp BoundedWord64.of_word64 rcarry_addW))
              (Interp (@Word64.interp_op)
                 (MapInterp (fun (t : base_type) (x : Word64.interp_base_type t) => x)
                    rcarry_addW))
  split. Focus 2.
  {

  cbv beta iota delta [interp_type_rel_pointwise2 interp_type_gen_rel_pointwise2 Morphisms.respectful_hetero interp_flat_type BoundedWord64.interp_base_type Z.interp_base_type interp_flat_type_rel_pointwise2 interp_flat_type_rel_pointwise2_gen_Prop Relations.related_Zi Relations.related_Z Relations.lift_relation Relations.related'_Z] in Hbounds.
  Set Printing Depth 100000.
    Arguments proj1_sig : clear implicits.



Admitted.
Lemma rsub_correct_and_bounded : binop_correct_and_bounded rsub carry_sub.
Proof.
Admitted.
Lemma rmul_correct_and_bounded : binop_correct_and_bounded rmul mul.
Proof.
Admitted.
Lemma ropp_correct_and_bounded : unop_correct_and_bounded ropp carry_opp.
Proof.
Admitted.
Lemma rfreeze_correct_and_bounded : unop_correct_and_bounded rfreeze freeze.
Proof.
Admitted.
Lemma rge_modulus_correct_and_bounded : unop_FEToZ_correct rge_modulus ge_modulus.
Proof.
Admitted.
Lemma rpack_correct_and_bounded : unop_FEToWire_correct_and_bounded rpack pack.
Proof.
Admitted.
Lemma runpack_correct_and_bounded : unop_WireToFE_correct_and_bounded runpack unpack.
Proof.
Admitted.
