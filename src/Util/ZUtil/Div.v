Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZUtil.Hints.
Local Open Scope Z_scope.

Module Z.
  Lemma div_mul' : forall a b : Z, b <> 0 -> (b * a) / b = a.
  Proof. intros. rewrite Z.mul_comm. apply Z.div_mul; auto. Qed.
  Hint Rewrite div_mul' using zutil_arith : zsimplify.
End Z.
