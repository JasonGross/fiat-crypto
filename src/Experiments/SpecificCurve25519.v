Require Import Crypto.Util.Notations Coq.ZArith.BinInt.
Require Import Crypto.Specific.GF25519.
Require Import Crypto.CompleteEdwardsCurve.ExtendedCoordinates.
Require Import Crypto.Util.LetIn.
Local Infix "<<" := Z.shiftr.
Local Infix "&" := Z.land.

Section Curve25519.
  Context {twice_d : fe25519}.

  Definition ge25519_add' :=
    Eval cbv beta delta [Extended.add_coordinates fe25519 add mul sub ModularBaseSystemOpt.Let_In] in
      @Extended.add_coordinates fe25519 add sub mul twice_d.

  Definition ge25519_add_sig : forall P1 P2, { r | r = ge25519_add' P1 P2 }.
    intros.
    repeat match goal with p:prod _ _ |- _ => destruct p end.
    eexists.
    cbv beta delta [ge25519_add'].
    replace_match_let_in_pair_with_let_in_match_pair.
    Print Ltac replace_match_let_in_pair_with_let_in_match_pair.
    
End Curve25519.