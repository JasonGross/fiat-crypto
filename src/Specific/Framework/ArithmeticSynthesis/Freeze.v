Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Arithmetic.Saturated.Freeze.
Require Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn Crypto.Util.ZUtil.Definitions.
Require Crypto.Util.Tuple.

Module Export Exports.
  Hint Opaque freeze : uncps.
  Hint Rewrite freeze_id : uncps.
End Exports.

Local Open Scope Z_scope.
Local Infix "^" := Tuple.tuple : type_scope.

(* kludge to get around name clashes in the following, and the fact
     that the python script cares about argument names *)
Local Ltac rewrite_eval_freeze_with_c c' :=
  rewrite eval_freeze with (c:=c').

Notation freeze_sig_type sz m wt :=
  {freeze : (Z^sz -> Z^sz)%type |
   forall a : Z^sz%nat%type,
     (0 <= Positional.eval wt a < 2 * Z.pos m)->
     let eval := Positional.Fdecode (m := m) wt in
     eval (freeze a) = eval a}
    (only parsing).

Ltac solve_freeze_sig c m_enc bitwidth wt_nonzero wt_pos wt_divides wt_multiples :=
  lazymatch goal with
  | [ |- freeze_sig_type ?sz ?m ?wt ]
    => let a := fresh "a" in
       eexists; cbv beta zeta; (intros a ?);
       pose proof wt_nonzero; pose proof wt_pos;
       pose proof div_mod; pose proof wt_divides;
       pose proof wt_multiples;
       pose proof div_correct; pose proof modulo_correct;
       let x := constr:(@freeze wt sz (Z.ones bitwidth) m_enc a) in
       F_mod_eq;
       transitivity (Positional.eval wt x); repeat autounfold;
       [ | autorewrite with uncps push_id push_basesystem_eval;
           rewrite_eval_freeze_with_c c;
           try eassumption; try omega; try reflexivity;
           try solve [auto using B.Positional.select_id,
                      B.Positional.eval_select(*, zselect_correct*)];
           vm_decide];
       cbv[mod_eq]; apply f_equal2;
       [  | reflexivity ]; apply f_equal;
       cbv - [runtime_opp runtime_add runtime_mul runtime_shr runtime_and Let_In Z.add_get_carry Z.zselect];
       reflexivity
  end.
