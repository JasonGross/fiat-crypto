Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.BoundedWord.
Require Import Crypto.Specific.IntegrationTestTemporaryMiscCommon.
Require Import Crypto.Compilers.Z.Bounds.Pipeline.
Require Import Crypto.Specific.ArithmeticSynthesisFramework.

Ltac assert_nsig_then package f_op sig_type cont :=
  let feBW' := fresh "feBW'" in
  let phi' := fresh "phi'" in
  pose (@feBW _ package) as feBW';
  pose (@phiBW _ package) as phi';
  let sig_ty := sig_type feBW' phi' in
  let sig_ty := (eval cbv beta in sig_ty) in
  assert (f_op : sig_ty);
  [ cont feBW' phi'
  | cbv delta [feBW' phi'] in f_op; clear feBW' phi' ].
Ltac preglue_nsig_with_carry package f_sig do_rewrite feBW' phi' :=
  let f_sig' := fresh "f_sig'" in
  let carry_sig' := fresh "carry_sig'" in
  pose (@f_sig _ package) as f_sig';
  pose (@carry_sig _ package) as carry_sig';
  cbv [package feBW phiBW f_sig carry_sig ASPackage ASParams] in * |- ;
  start_preglue;
  [ do_rewrite f_sig' carry_sig'; cbv_runtime | .. ];
  fin_preglue;
  subst feBW' phi' f_sig' carry_sig'.
Ltac preglue_nsig_with_bounded package f_sig feBW' phi' :=
  let feBW_bounded' := fresh "feBW_bounded'" in
  let f_sig' := fresh "f_sig'" in
  pose (@f_sig _ package) as f_sig';
  pose proof (@feBW_bounded _ package) as feBW_bounded';
  cbv [package feBW phiBW f_sig ASPackage ASParams] in * |- ;
  start_preglue;
  [ do_rewrite_with_sig_by f_sig' ltac:(fun _ => apply feBW_bounded'); cbv_runtime | .. ];
  fin_preglue;
  subst feBW' phi' f_sig';
  clear feBW_bounded'.
Ltac refine_reflectively_nsig package :=
  let allowable_bit_widths := constr:(@allowable_bit_widths package) in
  refine_reflectively_gen allowable_bit_widths default.
Ltac refine_reflectively_freeze package :=
  let freeze_allowable_bit_widths := constr:(@freeze_allowable_bit_widths package) in
  refine_reflectively_gen freeze_allowable_bit_widths anf.

Ltac pose_nsig_with_carry f_sig package f_op sig_type do_rewrite :=
  assert_nsig_then
    package f_op sig_type
    ltac:(fun feBW' phi'
          => preglue_nsig_with_carry package f_sig do_rewrite feBW' phi';
             refine_reflectively_nsig package).

Ltac assert_1sig_with_carry_then_preglue_then f_sig F_op package f_op cont :=
  assert_nsig_then
    package f_op
    ltac:(fun feBW' phi'
          => constr:({ f_op : feBW' -> feBW'
                     | forall a, phi' (f_op a) = F_op (phi' a) }))
    ltac:(fun feBW' phi'
          => preglue_nsig_with_carry package f_sig do_rewrite_with_1sig_add_carry feBW' phi';
             cont ()).

Ltac assert_2sig_with_carry_then_preglue_then f_sig F_op package f_op cont :=
  assert_nsig_then
    package f_op
    ltac:(fun feBW' phi'
          => constr:({ f_op : feBW' -> feBW' -> feBW'
                     | forall a b, phi' (f_op a b) = F_op (phi' a) (phi' b) }))
    ltac:(fun feBW' phi'
          => preglue_nsig_with_carry package f_sig do_rewrite_with_2sig_add_carry feBW' phi';
             cont ()).

Ltac pose_1sig_with_carry f_sig F_op package f_op :=
  assert_1sig_with_carry_then_preglue_then
    f_sig F_op package f_op
    ltac:(fun _ => refine_reflectively_nsig package).
Ltac pose_2sig_with_carry f_sig F_op package f_op :=
  assert_2sig_with_carry_then_preglue_then
    f_sig F_op package f_op
    ltac:(fun _ => refine_reflectively_nsig package).

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
    ltac:(fun feBW' phi' =>
            constr:({ freeze : feBW' -> feBW'
                    | forall a, phi' (freeze a) = phi' a }))
    ltac:(fun feBW' phi'
          => preglue_nsig_with_bounded package (@freeze_sig) feBW' phi';
             cont ()).

Ltac pose_freeze package freeze :=
  assert_freeze_then package freeze ltac:(fun _ => refine_reflectively_freeze package).
