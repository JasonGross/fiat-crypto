Require Import Crypto.Specific.Framework.ArithmeticSynthesis.BasePackage.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.DefaultsPackage.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.FreezePackage.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.KaratsubaPackage.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.LadderstepPackage.
Require Import Crypto.Specific.Framework.CurveParametersPackage.
Require Import Crypto.Specific.Framework.ReificationTypes.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.BoundedWord.
Require Import Crypto.Specific.Framework.IntegrationTestTemporaryMiscCommon.
Require Import Crypto.Compilers.Z.Bounds.Pipeline.

Module Export Exports.
  Export ArithmeticSynthesis.Defaults.Exports.
  Export ArithmeticSynthesis.Freeze.Exports.
End Exports.

Module MakeSynthesisTactics (Curve : CurveParameters.CurveParameters).
  Module P := FillCurveParameters Curve.

  Ltac get_synthesis_package _ :=
    let CurveParameters_pkg := P.get_CurveParameters_package () in
    let ArithmeticSynthesisBase_pkg := get_ArithmeticSynthesisBase_package CurveParameters_pkg in
    let ReificationTypes_pkg := get_ReificationTypes_package CurveParameters_pkg ArithmeticSynthesisBase_pkg P.upper_bound_of_exponent in
    let if_goldilocks tac_true tac_false arg
        := (P.choose
              CurveParameters_pkg
              ltac:(fun goldilocks montgomery
                    => lazymatch goldilocks with
                       | true => tac_true arg
                       | false => tac_false arg
                       end)) in
    let carry_sig := fresh "carry_sig" in
    let zero_sig := fresh "zero_sig" in
    let one_sig := fresh "one_sig" in
    let a24_sig := fresh "a24_sig" in
    let add_sig := fresh "add_sig" in
    let sub_sig := fresh "sub_sig" in
    let opp_sig := fresh "opp_sig" in
    let mul_sig := fresh "mul_sig" in
    let square_sig := fresh "square_sig" in
    let freeze_sig := fresh "freeze_sig" in
    let ring := fresh "ring" in
    let Mxzladderstep_sig := fresh "Mxzladderstep_sig" in
    let carry_sig := DefaultsPackage.pose_carry_sig CurveParameters_pkg ArithmeticSynthesisBase_pkg carry_sig in
    let zero_sig := DefaultsPackage.pose_zero_sig CurveParameters_pkg ArithmeticSynthesisBase_pkg zero_sig in
    let one_sig := DefaultsPackage.pose_one_sig CurveParameters_pkg ArithmeticSynthesisBase_pkg one_sig in
    let a24_sig := DefaultsPackage.pose_a24_sig CurveParameters_pkg ArithmeticSynthesisBase_pkg a24_sig in
    let add_sig := DefaultsPackage.pose_add_sig CurveParameters_pkg ArithmeticSynthesisBase_pkg add_sig in
    let sub_sig := DefaultsPackage.pose_sub_sig CurveParameters_pkg ArithmeticSynthesisBase_pkg sub_sig in
    let opp_sig := DefaultsPackage.pose_opp_sig CurveParameters_pkg ArithmeticSynthesisBase_pkg opp_sig in
    let mul_sig := if_goldilocks
                     ltac:(KaratsubaPackage.pose_mul_sig CurveParameters_pkg ArithmeticSynthesisBase_pkg)
                            ltac:(DefaultsPackage.pose_mul_sig CurveParameters_pkg ArithmeticSynthesisBase_pkg ltac:(fun _ => P.default_mul) ltac:(fun _ => P.extra_prove_mul_eq))
                                   mul_sig in
    let square_sig := if_goldilocks
                        ltac:(DefaultsPackage.pose_square_sig_from_mul_sig CurveParameters_pkg ArithmeticSynthesisBase_pkg mul_sig)
                               ltac:(DefaultsPackage.pose_square_sig CurveParameters_pkg ArithmeticSynthesisBase_pkg ltac:(fun _ => P.default_square) ltac:(fun _ => P.extra_prove_square_eq))
                                      square_sig in
    let freeze_sig := pose_freeze_sig CurveParameters_pkg ArithmeticSynthesisBase_pkg freeze_sig in
    let ring := DefaultsPackage.pose_ring CurveParameters_pkg ArithmeticSynthesisBase_pkg zero_sig one_sig opp_sig add_sig sub_sig mul_sig ring in
    let Mxzladderstep_sig := pose_Mxzladderstep_sig CurveParameters_pkg ArithmeticSynthesisBase_pkg add_sig sub_sig mul_sig square_sig carry_sig Mxzladderstep_sig in
    constr:((CurveParameters_pkg,
             ArithmeticSynthesisBase_pkg,
             ReificationTypes_pkg,
             (carry_sig, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, mul_sig, square_sig, freeze_sig, ring, Mxzladderstep_sig))).

  Ltac make_synthesis_package _ :=
    lazymatch goal with
    | [ |- { T : _ & _ } ]
      => first [ eexists (_, _, _, _)
               | eexists (_, _, _)
               | eexists (_, _)
               | eexists ]
    | [ |- _ ] => idtac
    end;
    let pkg := get_synthesis_package () in
    exact pkg.
End MakeSynthesisTactics.

Local Notation eta2 x := (fst x, snd x) (only parsing).
Local Notation eta3 x := (eta2 (fst x), snd x) (only parsing).
Local Notation eta4 x := (eta3 (fst x), snd x) (only parsing).

Notation Synthesis_package'_Type :=
  { T : _ & let '(a, b, c, d) := eta4 T in (a * b * c * d)%type } (only parsing).

Module Type SynthesisPrePackage.
  Parameter Synthesis_package' : Synthesis_package'_Type.
  Parameter Synthesis_package : let '(a, b, c, d) := eta4 (projT1 Synthesis_package') in (a * b * c * d)%type.
End SynthesisPrePackage.

Module PackageSynthesis (Curve : CurveParameters.CurveParameters) (P : SynthesisPrePackage).
  Module CP := CurveParameters.FillCurveParameters Curve.

  Module PP <:
    CurveParametersPrePackage <:
    ArithmeticSynthesisBasePrePackage <:
    ReificationTypesPrePackage.

    Definition CurveParameters_package := Eval compute in let '(a, b, c, d) := P.Synthesis_package in a.
    Definition CurveParameters_package' : { T : _ & T } := existT _ _ CurveParameters_package.
    Definition ArithmeticSynthesisBase_package := Eval compute in let '(a, b, c, d) := P.Synthesis_package in b.
    Definition ArithmeticSynthesisBase_package' : { T : _ & T } := existT _ _ ArithmeticSynthesisBase_package.
    Definition ReificationTypes_package := Eval compute in let '(a, b, c, d) := P.Synthesis_package in c.
    Definition ReificationTypes_package' : { T : _ & T } := existT _ _ ReificationTypes_package.
    Definition FullSynthesis_package := Eval compute in let '(a, b, c, d) := P.Synthesis_package in d.
    Definition FullSynthesis_package' : { T : _ & T } := existT _ _ FullSynthesis_package.
  End PP.
  Module CS := MakeCurveParametersTest PP.
  Module RT := MakeReificationTypes PP.
  Module AS := MakeArithmeticSynthesisBaseTest PP.
  Include CS.
  Include RT.
  Include AS.

  Module FS.
    Ltac get_FullSynthesis_package _ := eval hnf in PP.FullSynthesis_package.
    Ltac FS_reduce_proj x :=
      eval cbv beta iota zeta in x.
  (**
<<
terms = 'carry_sig, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, mul_sig, square_sig, freeze_sig, ring, Mxzladderstep_sig'
for i in terms.split(', '):
    print("    Ltac get_%s _ := let pkg := get_FullSynthesis_package () in FS_reduce_proj (let '(%s) := pkg in %s)." % (i, terms, i))
    print("    Notation %s := (ltac:(let v := get_%s () in exact v)) (only parsing)." % (i, i))
>> *)
    Ltac get_carry_sig _ := let pkg := get_FullSynthesis_package () in FS_reduce_proj (let '(carry_sig, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, mul_sig, square_sig, freeze_sig, ring, Mxzladderstep_sig) := pkg in carry_sig).
    Notation carry_sig := (ltac:(let v := get_carry_sig () in exact v)) (only parsing).
    Ltac get_zero_sig _ := let pkg := get_FullSynthesis_package () in FS_reduce_proj (let '(carry_sig, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, mul_sig, square_sig, freeze_sig, ring, Mxzladderstep_sig) := pkg in zero_sig).
    Notation zero_sig := (ltac:(let v := get_zero_sig () in exact v)) (only parsing).
    Ltac get_one_sig _ := let pkg := get_FullSynthesis_package () in FS_reduce_proj (let '(carry_sig, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, mul_sig, square_sig, freeze_sig, ring, Mxzladderstep_sig) := pkg in one_sig).
    Notation one_sig := (ltac:(let v := get_one_sig () in exact v)) (only parsing).
    Ltac get_a24_sig _ := let pkg := get_FullSynthesis_package () in FS_reduce_proj (let '(carry_sig, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, mul_sig, square_sig, freeze_sig, ring, Mxzladderstep_sig) := pkg in a24_sig).
    Notation a24_sig := (ltac:(let v := get_a24_sig () in exact v)) (only parsing).
    Ltac get_add_sig _ := let pkg := get_FullSynthesis_package () in FS_reduce_proj (let '(carry_sig, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, mul_sig, square_sig, freeze_sig, ring, Mxzladderstep_sig) := pkg in add_sig).
    Notation add_sig := (ltac:(let v := get_add_sig () in exact v)) (only parsing).
    Ltac get_sub_sig _ := let pkg := get_FullSynthesis_package () in FS_reduce_proj (let '(carry_sig, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, mul_sig, square_sig, freeze_sig, ring, Mxzladderstep_sig) := pkg in sub_sig).
    Notation sub_sig := (ltac:(let v := get_sub_sig () in exact v)) (only parsing).
    Ltac get_opp_sig _ := let pkg := get_FullSynthesis_package () in FS_reduce_proj (let '(carry_sig, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, mul_sig, square_sig, freeze_sig, ring, Mxzladderstep_sig) := pkg in opp_sig).
    Notation opp_sig := (ltac:(let v := get_opp_sig () in exact v)) (only parsing).
    Ltac get_mul_sig _ := let pkg := get_FullSynthesis_package () in FS_reduce_proj (let '(carry_sig, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, mul_sig, square_sig, freeze_sig, ring, Mxzladderstep_sig) := pkg in mul_sig).
    Notation mul_sig := (ltac:(let v := get_mul_sig () in exact v)) (only parsing).
    Ltac get_square_sig _ := let pkg := get_FullSynthesis_package () in FS_reduce_proj (let '(carry_sig, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, mul_sig, square_sig, freeze_sig, ring, Mxzladderstep_sig) := pkg in square_sig).
    Notation square_sig := (ltac:(let v := get_square_sig () in exact v)) (only parsing).
    Ltac get_freeze_sig _ := let pkg := get_FullSynthesis_package () in FS_reduce_proj (let '(carry_sig, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, mul_sig, square_sig, freeze_sig, ring, Mxzladderstep_sig) := pkg in freeze_sig).
    Notation freeze_sig := (ltac:(let v := get_freeze_sig () in exact v)) (only parsing).
    Ltac get_ring _ := let pkg := get_FullSynthesis_package () in FS_reduce_proj (let '(carry_sig, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, mul_sig, square_sig, freeze_sig, ring, Mxzladderstep_sig) := pkg in ring).
    Notation ring := (ltac:(let v := get_ring () in exact v)) (only parsing).
    Ltac get_Mxzladderstep_sig _ := let pkg := get_FullSynthesis_package () in FS_reduce_proj (let '(carry_sig, zero_sig, one_sig, a24_sig, add_sig, sub_sig, opp_sig, mul_sig, square_sig, freeze_sig, ring, Mxzladderstep_sig) := pkg in Mxzladderstep_sig).
    Notation Mxzladderstep_sig := (ltac:(let v := get_Mxzladderstep_sig () in exact v)) (only parsing).
  End FS.
  Include FS.

  Ltac synthesize_with_carry do_rewrite get_op_sig :=
    let carry_sig := get_carry_sig () in
    let op_sig := get_op_sig () in
    start_preglue;
    [ do_rewrite op_sig carry_sig; cbv_runtime
    | .. ];
    fin_preglue;
    refine_reflectively_gen CP.allowable_bit_widths default.
  Ltac synthesize_2arg_with_carry get_op_sig :=
    synthesize_with_carry do_rewrite_with_2sig_add_carry get_op_sig.
  Ltac synthesize_1arg_with_carry get_op_sig :=
    synthesize_with_carry do_rewrite_with_1sig_add_carry get_op_sig.

  Ltac synthesize_mul _ := synthesize_2arg_with_carry get_mul_sig.
  Ltac synthesize_add _ := synthesize_2arg_with_carry get_add_sig.
  Ltac synthesize_sub _ := synthesize_2arg_with_carry get_sub_sig.
  Ltac synthesize_square _ := synthesize_1arg_with_carry get_square_sig.
  Ltac synthesize_freeze _ :=
    let freeze_sig := get_freeze_sig () in
    let feBW_bounded := get_feBW_bounded () in
    start_preglue;
    [ do_rewrite_with_sig_by freeze_sig ltac:(fun _ => apply feBW_bounded); cbv_runtime
    | .. ];
    fin_preglue;
    refine_reflectively_gen CP.freeze_allowable_bit_widths anf.
  Ltac synthesize_xzladderstep _ :=
    let Mxzladderstep_sig := get_Mxzladderstep_sig () in
    let a24_sig := get_a24_sig () in
    start_preglue;
    [ unmap_map_tuple ();
      do_rewrite_with_sig_1arg Mxzladderstep_sig;
      cbv [Mxzladderstep XZ.M.xzladderstep a24_sig]; cbn [proj1_sig];
      do_set_sigs ();
      cbv_runtime
    | .. ];
    finish_conjoined_preglue ();
    refine_reflectively_gen CP.allowable_bit_widths default.
End PackageSynthesis.
