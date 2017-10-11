Require Export Coq.ZArith.BinInt.
Require Export Coq.Lists.List.
Require Export Crypto.Util.ZUtil.Notations.
Require Crypto.Util.Tuple.

Module Export Notations.
  Export ListNotations.

  Open Scope list_scope.
  Open Scope Z_scope.

  Notation limb := (Z * Z)%type.
  Infix "^" := Tuple.tuple : type_scope.
End Notations.

(* These definitions will need to be passed as Ltac arguments (or
   cleverly inferred) when things are eventually automated *)
Module Type CurveParameters.
  Parameter sz : nat.
  Parameter bitwidth : Z.
  Parameter s : Z.
  Parameter c : list limb.
  Parameter carry_chains
    : option (list (list nat)). (* defaults to [seq 0 (pred sz) :: (0 :: 1 :: nil) :: nil] *)
  Parameter a24 : option Z.
  Parameter coef_div_modulus : option nat.

  Parameter goldilocks : bool.
  Parameter montgomery : bool.

  Parameter mul_code : option (Z^sz -> Z^sz -> Z^sz).
  Parameter square_code : option (Z^sz -> Z^sz).
  Parameter upper_bound_of_exponent
    : option (Z -> Z). (* defaults to [fun exp => 2^exp + 2^(exp-3)] *)
  Parameter allowable_bit_widths
    : option (list nat). (* defaults to [bitwidth :: 2*bitwidth :: nil] *)
  Parameter freeze_extra_allowable_bit_widths
    : option (list nat). (* defaults to [8 :: nil] *)
  Parameter modinv_fuel : option nat.
  Ltac extra_prove_mul_eq := idtac.
  Ltac extra_prove_square_eq := idtac.
End CurveParameters.

Module FillCurveParameters (P : CurveParameters).
  Local Notation defaulted opt_v default
    := (match opt_v with
        | Some v => v
        | None => default
        end).
  Ltac do_compute v :=
    let v' := (eval vm_compute in v) in v'.
  Notation compute v
    := (ltac:(let v' := do_compute v in exact v'))
         (only parsing).
  Definition sz := P.sz.
  Definition bitwidth := P.bitwidth.
  Definition s := P.s.
  Definition c := P.c.
  Definition carry_chains := defaulted P.carry_chains [seq 0 (pred sz); [0; 1]]%nat.
  Definition a24 := defaulted P.a24 0.
  Definition coef_div_modulus := defaulted P.coef_div_modulus 0%nat.

  Definition goldilocks := P.goldilocks.
  Definition montgomery := P.montgomery.

  Ltac default_mul :=
    lazymatch (eval hnf in P.mul_code) with
    | None => reflexivity
    | Some ?mul_code
      => instantiate (1:=mul_code)
    end.
  Ltac default_square :=
    lazymatch (eval hnf in P.square_code) with
    | None => reflexivity
    | Some ?square_code
      => instantiate (1:=square_code)
    end.

  Definition upper_bound_of_exponent
    := defaulted P.upper_bound_of_exponent
                 (if P.montgomery
                  then (fun exp => (2^exp - 1)%Z)
                  else (fun exp => (2^exp + 2^(exp-3))%Z)).
  Local Notation list_8_if_not_exists ls :=
    (if existsb (Nat.eqb 8) ls
     then nil
     else [8]%nat)
      (only parsing).
  Definition allowable_bit_widths
    := defaulted
         P.allowable_bit_widths
         ((if P.montgomery
           then [8]
           else nil)
            ++ (Z.to_nat bitwidth :: 2*Z.to_nat bitwidth :: nil))%nat.
  Definition freeze_allowable_bit_widths
    := defaulted
         P.freeze_extra_allowable_bit_widths
         (list_8_if_not_exists allowable_bit_widths)
         ++ allowable_bit_widths.
  Definition modinv_fuel := defaulted P.modinv_fuel 10%nat.

  (* hack around https://coq.inria.fr/bugs/show_bug.cgi?id=5764 *)
  Ltac do_unfold v' :=
    let P_sz := P.sz in
    let P_bitwidth := P.bitwidth in
    let P_s := P.s in
    let P_c := P.c in
    let P_carry_chains := P.carry_chains in
    let P_a24 := P.a24 in
    let P_coef_div_modulus := P.coef_div_modulus in
    let P_goldilocks := P.goldilocks in
    let P_montgomery := P.montgomery in
    let P_mul_code := P.mul_code in
    let P_square_code := P.square_code in
    let P_upper_bound_of_exponent := P.upper_bound_of_exponent in
    let P_allowable_bit_widths := P.allowable_bit_widths in
    let P_freeze_extra_allowable_bit_widths := P.freeze_extra_allowable_bit_widths in
    let P_modinv_fuel := P.modinv_fuel in
    let v' := (eval cbv [id
                           List.app
                           sz bitwidth s c carry_chains a24 coef_div_modulus goldilocks montgomery modinv_fuel
                           P_sz P_bitwidth P_s P_c P_carry_chains P_a24 P_coef_div_modulus P_goldilocks P_montgomery P_modinv_fuel
                           P_mul_code P_square_code
                           upper_bound_of_exponent allowable_bit_widths freeze_allowable_bit_widths
                           P_upper_bound_of_exponent P_allowable_bit_widths P_freeze_extra_allowable_bit_widths
                           pred seq]
                in v') in
    v'.
  Notation unfold v
   := (ltac:(let v' := v in
              let v' := do_unfold v' in
              exact v'))
         (only parsing).
  Ltac extra_prove_mul_eq := P.extra_prove_mul_eq.
  Ltac extra_prove_square_eq := P.extra_prove_square_eq.

  Local Notation P_sz := sz.
  Local Notation P_bitwidth := bitwidth.
  Local Notation P_s := s.
  Local Notation P_c := c.
  Local Notation P_carry_chains := carry_chains.
  Local Notation P_a24 := a24.
  Local Notation P_coef_div_modulus := coef_div_modulus.
  Local Notation P_goldilocks := goldilocks.
  Local Notation P_montgomery := montgomery.
  Local Notation P_upper_bound_of_exponent := upper_bound_of_exponent.
  Local Notation P_allowable_bit_widths := allowable_bit_widths.
  Local Notation P_freeze_allowable_bit_widths := freeze_allowable_bit_widths.
  Local Notation P_modinv_fuel := modinv_fuel.

  Module Export Solvers.
    Notation sz_type :=
      nat
        (only parsing).

    Ltac solve_sz :=
      lazymatch goal with
      | [ |- sz_type ]
        => let v := do_compute P_sz in exact v
      end.
    Notation bitwidth_type :=
      Z
        (only parsing).
    Ltac solve_bitwidth :=
      lazymatch goal with
      | [ |- bitwidth_type ]
        => let v := do_compute P_bitwidth in exact v
      end.
    Notation s_type :=
      Z
        (only parsing).
    Ltac solve_s := (* don't want to compute, e.g., [2^255] *)
      lazymatch goal with
      | [ |- s_type ]
        => let v := do_unfold P_s in exact v
      end.
    Notation c_type :=
      (list limb)
        (only parsing).
    Ltac solve_c :=
      lazymatch goal with
      | [ |- c_type ]
        => let v := do_compute P_c in exact v
      end.
    Ltac solve_carry_chains :=
      let v := do_compute P_carry_chains in
      exact v.

    Ltac solve_a24 :=
      let v := do_compute P_a24 in
      exact v.
    Notation coef_div_modulus_type :=
      nat
        (only parsing).
    Ltac solve_coef_div_modulus :=
      lazymatch goal with
      | [ |- coef_div_modulus_type ]
        => let v := do_compute P_coef_div_modulus in exact v
      end.
    Notation goldilocks_type :=
      bool
        (only parsing).
    Ltac solve_goldilocks :=
      lazymatch goal with
      | [ |- goldilocks_type ]
        => let v := do_compute P_goldilocks in exact v
      end.
    Notation montgomery_type :=
      bool
        (only parsing).
    Ltac solve_montgomery :=
      lazymatch goal with
      | [ |- montgomery_type ]
        => let v := do_compute P_montgomery in exact v
      end.

    Notation modinv_fuel_type :=
      nat
        (only parsing).

    Ltac solve_modinv_fuel :=
      lazymatch goal with
      | [ |- modinv_fuel_type ]
        => let v := do_compute P_modinv_fuel in exact v
      end.

    Notation upper_bound_of_exponent_type :=
      (Z -> Z)
        (only parsing).

    Ltac solve_upper_bound_of_exponent :=
      lazymatch goal with
      | [ |- upper_bound_of_exponent_type ]
        => let v := do_unfold P_upper_bound_of_exponent in exact v
      end.

    Ltac if_cond_else cond tac_true tac_false :=
      lazymatch (eval compute in cond) with
      | true => tac_true
      | false => tac_false
      end.

    Ltac if_goldilocks := if_cond_else P.goldilocks.
    Ltac if_montgomery := if_cond_else P.montgomery.

    Notation if_goldilocks ifyes ifno :=
      ltac:(let v := if_goldilocks ifyes ifno in exact v)
             (only parsing).
    Notation if_montgomery ifyes ifno :=
      ltac:(let v := if_montgomery ifyes ifno in exact v)
             (only parsing).
  End Solvers.
End FillCurveParameters.
