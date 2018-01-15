Require Import Crypto.Specific.CurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : 2^255-19
Base: 51
***)

Module Curve <: CurveParameters.
  Definition sz : nat := 5%nat.
  Definition bitwidth : Z := 64.
  Definition s : Z := 2^256.
  Definition c : list limb := [(1, 2^32+977)].
  (*Definition carry_chain1 := Eval vm_compute in Some (seq 0 (pred sz)).
  Definition carry_chain2 := Some [0;1]%nat.*)
  Definition carry_chain1 := Some [0;1;2;3;4]%nat.
  Definition carry_chain2 := Some [0;1;2;3;4;0;1]%nat.
  Definition limb_widths := [52; 52; 52; 52; 48]%Z.

  Definition a24 := 121665%Z.
  Definition coef_div_modulus : nat := 2. (* add 2*modulus before subtracting *)

  Definition mul_code : option (Z^sz -> Z^sz -> Z^sz) := None.
  Definition square_code : option (Z^sz -> Z^sz) := None.

  Definition upper_bound_of_exponent : option (Z -> Z) := None.
  Definition allowable_bit_widths : option (list nat) := None.
  Definition freeze_extra_allowable_bit_widths : option (list nat) := None.
  Ltac extra_prove_mul_eq := idtac.
  Ltac extra_prove_square_eq := idtac.
End Curve.
