(** * Definitions of some basic operations on ℤ used in ModularBaseSystemList *)
(** We separate these out so that we can depend on them in other files
    without waiting for ModularBaseSystemList to build. *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.

Definition cmovl (x y r1 r2 : Z) := if Z.leb x y then r1 else r2.
Definition cmovne (x y r1 r2 : Z) := if Z.eqb x y then r1 else r2.

(* analagous to NEG assembly instruction on an integer that is 0 or 1:
   neg 1 = 2^64 - 1 (on 64-bit; 2^32-1 on 32-bit, etc.)
   neg 0 = 0 *)
Definition neg (int_width : Z) (b : Z) := if Z.eqb b 1 then Z.ones int_width else 0%Z.

Section conditional_subtract_modulus.
  Context (limb_count : nat) (int_width : Z) (modulus : Tuple.tuple Z limb_count).
  Local Notation "u [ i ]" := (List.nth_default 0%Z (Tuple.to_list _ u) i).

  (* Constant-time comparison with modulus; only works if all digits of [us]
    are less than 2 ^ their respective limb width. *)
  Fixpoint ge_modulus' {A} (f : Z -> A) (us : Tuple.tuple Z limb_count) (result : Z) i :=
    dlet r := result in
    match i return A with
    | O =>
      dlet x := (cmovl (modulus [0]) (us [0]) r 0) in f x
    | S i' =>
      ge_modulus' f us (cmovne (modulus [i]) (us [i]) r 0) i'
    end.

  Definition ge_modulus us := ge_modulus' id us 1 (limb_count - 1)%nat.

  Definition conditional_subtract_modulus (us : Tuple.tuple Z limb_count) :=
    (* [and_term] is all ones if us' is full, so the subtractions subtract q overall.
       Otherwise, it's all zeroes, and the subtractions do nothing. *)
    Tuple.map2 (fun x y => x - y)%Z
               us
               (map (Z.land (neg int_width (ge_modulus us))) modulus).
End conditional_subtract_modulus.
