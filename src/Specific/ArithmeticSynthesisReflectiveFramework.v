Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.BoundedWord.
Require Import Crypto.Specific.IntegrationTestTemporaryMiscCommon.
Require Import Crypto.Compilers.Z.Bounds.Pipeline.
Require Import Crypto.Specific.ArithmeticSynthesisFramework.
Require Import Crypto.Util.Tactics.CacheTerm.

Ltac eval_package_red_in package term :=
  let term := (eval cbv [id
                           package
                           ASParams
                           ASPackage
                           m
                           sz
                           a24
                           wt
                           a24_sig
                           add_sig
                           sub_sig
                           opp_sig
                           mul_sig
                           square_sig
                           carry_sig
                           freeze_sig
                           lgbitwidth
                           adjusted_bitwidth
                           bounds
                           feW
                           feBW
                           phiW
                           phiBW
                           feW_bounded
                           feBW_to_Z
                           feBW_bounded
                           allowable_bit_widths
                           freeze_allowable_bit_widths] in term) in
  term.

Ltac assert_nsig_then package f_op sig_type cont :=
  let feBW' := fresh "feBW'" in
  let phi' := fresh "phi'" in
  let feBW := (eval_package_red_in package (@feBW _ package)) in
  let phi := (eval_package_red_in package (@phiBW _ package)) in
  let feBW := cache_term feBW feBW' in
  let phi := cache_term phi phi' in
  let sig_ty := sig_type feBW phi in
  let sig_ty := (eval cbv beta in sig_ty) in
  assert (f_op : sig_ty);
  [ cont feBW phi
  | ].
Ltac preglue_nsig_with_carry package f_sig do_rewrite feBW' phi' :=
  let f_sig' := fresh "f_sig'" in
  let carry_sig' := fresh "carry_sig'" in
  let f_sig := (eval_package_red_in package (@f_sig _ package)) in
  let carry_sig := (eval_package_red_in package (@carry_sig _ package)) in
  start_preglue;
  [ do_rewrite f_sig carry_sig; cbv_runtime; cbv zeta iota beta | .. ];
  fin_preglue.
Ltac preglue_nsig_with_bounded package f_sig feBW' phi' :=
  let f_sig' := fresh "f_sig'" in
  let feBW_bounded' := fresh "feBW_bounded'" in
  let f_sig := (eval_package_red_in package (@f_sig _ package)) in
  let feBW_bounded := (eval_package_red_in package (@feBW_bounded _ package)) in
  start_preglue;
  [ do_rewrite_with_sig_by f_sig ltac:(fun _ => apply feBW_bounded); cbv_runtime | .. ];
  fin_preglue.
Ltac refine_reflectively_nsig package :=
  let allowable_bit_widths := constr:(@allowable_bit_widths package) in
  refine_reflectively_gen allowable_bit_widths default.
Ltac refine_reflectively_freeze package :=
  let freeze_allowable_bit_widths := constr:(@freeze_allowable_bit_widths package) in
  refine_reflectively_gen freeze_allowable_bit_widths anf.

Ltac pose_nsig_with_carry f_sig package f_op sig_type do_rewrite :=
  assert_nsig_then
    package f_op sig_type
    ltac:(fun feBW phi
          => preglue_nsig_with_carry package f_sig do_rewrite feBW phi;
             refine_reflectively_nsig package).

Ltac assert_1sig_with_carry_then f_sig F_op package f_op cont :=
  assert_nsig_then
    package f_op
    ltac:(fun feBW phi
          => constr:({ f_op : feBW -> feBW
                     | forall a, phi (f_op a) = F_op (phi a) }))
           cont.

Ltac assert_2sig_with_carry_then f_sig F_op package f_op cont :=
  assert_nsig_then
    package f_op
    ltac:(fun feBW phi
          => constr:({ f_op : feBW -> feBW -> feBW
                     | forall a b, phi (f_op a b) = F_op (phi a) (phi b) }))
           cont.

Ltac assert_1sig_with_carry_then_preglue_then f_sig F_op package f_op cont :=
  assert_1sig_with_carry_then
    f_sig F_op package f_op
    ltac:(fun feBW phi
          => preglue_nsig_with_carry package f_sig do_rewrite_with_1sig_add_carry feBW phi;
             cont ()).

Ltac assert_2sig_with_carry_then_preglue_then f_sig F_op package f_op cont :=
  assert_2sig_with_carry_then
    f_sig F_op package f_op
    ltac:(fun feBW phi
          => preglue_nsig_with_carry package f_sig do_rewrite_with_2sig_add_carry feBW phi;
             cont ()).

Ltac pose_1sig_with_carry f_sig F_op package f_op :=
  assert_1sig_with_carry_then_preglue_then
    f_sig F_op package f_op
    ltac:(fun _ => refine_reflectively_nsig package).
Ltac pose_2sig_with_carry f_sig F_op package f_op :=
  assert_2sig_with_carry_then_preglue_then
    f_sig F_op package f_op
    ltac:(fun _ => refine_reflectively_nsig package).

Ltac assert_mul package mul :=
  assert_2sig_with_carry_then (@mul_sig) (F.mul (m:=@m package)) package mul ltac:(fun _ _ => idtac).
Ltac assert_add package add :=
  assert_2sig_with_carry_then (@add_sig) (F.add (m:=@m package)) package add ltac:(fun _ _ => idtac).
Ltac assert_sub package sub :=
  assert_2sig_with_carry_then (@sub_sig) (F.sub (m:=@m package)) package sub ltac:(fun _ _ => idtac).
Ltac assert_square package square :=
  assert_1sig_with_carry_then (@square_sig) (fun a => F.mul (m:=@m package) a a) package square ltac:(fun _ _ => idtac).

Ltac assert_mul_then_preglue package mul :=
  assert_2sig_with_carry_then_preglue_then (@mul_sig) (F.mul (m:=@m package)) package mul ltac:(fun _ => idtac).
Ltac assert_add_then_preglue package add :=
  assert_2sig_with_carry_then_preglue_then (@add_sig) (F.add (m:=@m package)) package add ltac:(fun _ => idtac).
Ltac assert_sub_then_preglue package sub :=
  assert_2sig_with_carry_then_preglue_then (@sub_sig) (F.sub (m:=@m package)) package sub ltac:(fun _ => idtac).
Ltac assert_square_then_preglue package square :=
  assert_1sig_with_carry_then_preglue_then (@square_sig) (fun a => F.mul (m:=@m package) a a) package square ltac:(fun _ => idtac).

Ltac pose_mul package mul :=
  pose_2sig_with_carry (@mul_sig) (F.mul (m:=@m package)) package mul.
Ltac pose_add package add :=
  pose_2sig_with_carry (@add_sig) (F.add (m:=@m package)) package add.
Ltac pose_sub package sub :=
  pose_2sig_with_carry (@sub_sig) (F.sub (m:=@m package)) package sub.
Ltac pose_square package square :=
  pose_1sig_with_carry (@square_sig) (fun a => F.mul (m:=@m package) a a) package square.

Ltac assert_freeze_then package freeze cont :=
  assert_nsig_then
    package freeze
    ltac:(fun feBW phi =>
            constr:({ freeze : feBW -> feBW
                    | forall a, phi (freeze a) = phi a }))
    ltac:(fun feBW phi
          => preglue_nsig_with_bounded package (@freeze_sig) feBW phi;
             cont ()).

Ltac pose_freeze package freeze :=
  assert_freeze_then package freeze ltac:(fun _ => refine_reflectively_freeze package).
