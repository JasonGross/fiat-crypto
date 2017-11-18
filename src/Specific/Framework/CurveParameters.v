Require Import Coq.QArith.Qround.
Require Export Coq.ZArith.BinInt.
Require Export Coq.Lists.List.
Require Export Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.Tactics.CacheTerm.
Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.TagList.
Require Crypto.Util.Tuple.

Local Set Primitive Projections.

Module Export Notations := RawCurveParameters.Notations.

Module TAG. (* namespacing *)
  Inductive tags := CP | sz | base | bitwidth | s | c | carry_chains | a24 | coef_div_modulus | goldilocks | karatsuba | montgomery | freeze | upper_bound_of_exponent_tight | upper_bound_of_exponent_loose | allowable_bit_widths | freeze_allowable_bit_widths | modinv_fuel | mul_code | square_code.
End TAG.

Module Export CurveParameters.
  Local Notation eval p :=
    (List.fold_right Z.add 0%Z (List.map (fun t => fst t * snd t) p)).

  Ltac do_compute v :=
    let v' := (eval vm_compute in v) in v'.
  Notation compute v
    := (ltac:(let v' := do_compute v in exact v'))
         (only parsing).
  Local Notation defaulted opt_v default
    := (match opt_v with
        | Some v => v
        | None => default
        end)
         (only parsing).
  Record CurveParameters :=
    {
      sz : nat;
      base : Q;
      bitwidth : Z;
      s : Z;
      c : list limb;
      carry_chains : list (list nat);
      a24 : option Z;
      coef_div_modulus : nat;

      goldilocks : bool;
      karatsuba : bool;
      montgomery : bool;
      freeze : bool;

      mul_code : option (Z^sz -> Z^sz -> Z^sz);
      square_code : option (Z^sz -> Z^sz);
      upper_bound_of_exponent_tight : Z -> Z;
      upper_bound_of_exponent_loose : Z -> Z;
      allowable_bit_widths : list nat;
      freeze_allowable_bit_widths : list nat;
      modinv_fuel : nat
    }.

  Declare Reduction cbv_CurveParameters
    := cbv [sz
              base
              bitwidth
              s
              c
              carry_chains
              a24
              coef_div_modulus
              goldilocks
              karatsuba
              montgomery
              freeze
              mul_code
              square_code
              upper_bound_of_exponent_tight
              upper_bound_of_exponent_loose
              allowable_bit_widths
              freeze_allowable_bit_widths
              modinv_fuel].
  Ltac cbv_CurveParameters
    := cbv [sz
              base
              bitwidth
              s
              c
              carry_chains
              a24
              coef_div_modulus
              goldilocks
              karatsuba
              montgomery
              freeze
              mul_code
              square_code
              upper_bound_of_exponent_tight
              upper_bound_of_exponent_loose
              allowable_bit_widths
              freeze_allowable_bit_widths
              modinv_fuel].
  Ltac cbv_CurveParameters_in_all
    := cbv [sz
              base
              bitwidth
              s
              c
              carry_chains
              a24
              coef_div_modulus
              goldilocks
              karatsuba
              montgomery
              freeze
              mul_code
              square_code
              upper_bound_of_exponent_tight
              upper_bound_of_exponent_loose
              allowable_bit_widths
              freeze_allowable_bit_widths
              modinv_fuel] in *.

  Ltac default_mul CP :=
    lazymatch (eval hnf in (mul_code CP)) with
    | None => reflexivity
    | Some ?mul_code
      => instantiate (1:=mul_code)
    end.
  Ltac default_square CP :=
    lazymatch (eval hnf in (square_code CP)) with
    | None => reflexivity
    | Some ?square_code
      => instantiate (1:=square_code)
    end.

  Local Notation list_8_if_not_exists ls :=
    (if existsb (Nat.eqb 8) ls
     then nil
     else [8]%nat)
      (only parsing).

  Definition fill_defaults_CurveParameters (CP : RawCurveParameters.CurveParameters)
    : CurveParameters
    := Eval cbv_RawCurveParameters in
        let sz := RawCurveParameters.sz CP in
        let base := RawCurveParameters.base CP in
        let bitwidth := RawCurveParameters.bitwidth CP in
        let montgomery := RawCurveParameters.montgomery CP in
        let karatsuba := defaulted (RawCurveParameters.karatsuba CP) false in
        let s := RawCurveParameters.s CP in
        let c := RawCurveParameters.c CP in
        let freeze
            := defaulted
                 (RawCurveParameters.freeze CP)
                 (s =? 2^(Qceiling (base * sz))) in
        let goldilocks :=
            defaulted
              (RawCurveParameters.goldilocks CP)
              (let k := Z.log2 s / 2 in
               (s - eval c) =? (2^(2*k) - 2^k - 1)) in
        let allowable_bit_widths
            := defaulted
                 (RawCurveParameters.allowable_bit_widths CP)
                 ((if montgomery
                   then [8]
                   else nil)
                    ++ (Z.to_nat bitwidth :: 2*Z.to_nat bitwidth :: nil))%nat in
        let upper_bound_of_exponent_tight
            := defaulted (RawCurveParameters.upper_bound_of_exponent_tight CP)
                         (if montgomery
                          then (fun exp => (2^exp - 1)%Z)
                          else (fun exp => (2^exp + 2^(exp-3))%Z))
        (* max is [(0, 2^(exp+2) + 2^exp + 2^(exp-1) + 2^(exp-3) + 2^(exp-4) + 2^(exp-5) + 2^(exp-6) + 2^(exp-10) + 2^(exp-12) + 2^(exp-13) + 2^(exp-14) + 2^(exp-15) + 2^(exp-17) + 2^(exp-23) + 2^(exp-24))%Z] *) in
        let upper_bound_of_exponent_loose
            := defaulted (RawCurveParameters.upper_bound_of_exponent_loose CP)
                         (if montgomery
                          then (fun exp => (2^exp - 1)%Z)
                          else (fun exp => (3 * upper_bound_of_exponent_tight exp)%Z)) in
        {|
          sz := sz;
          base := base;
          bitwidth := bitwidth;
          s := s;
          c := c;
          carry_chains := defaulted (RawCurveParameters.carry_chains CP) [seq 0 (pred sz); [0; 1]]%nat;
          a24 := RawCurveParameters.a24 CP;
          coef_div_modulus := defaulted (RawCurveParameters.coef_div_modulus CP) 0%nat;

          goldilocks := goldilocks;
          karatsuba := karatsuba;
          montgomery := montgomery;
          freeze := freeze;

          mul_code := RawCurveParameters.mul_code CP;
          square_code := RawCurveParameters.square_code CP;
          upper_bound_of_exponent_tight := upper_bound_of_exponent_tight;
          upper_bound_of_exponent_loose := upper_bound_of_exponent_loose;

          allowable_bit_widths := allowable_bit_widths;
          freeze_allowable_bit_widths
          := defaulted
               (RawCurveParameters.freeze_extra_allowable_bit_widths CP)
               (list_8_if_not_exists allowable_bit_widths)
               ++ allowable_bit_widths;
          modinv_fuel := defaulted (RawCurveParameters.modinv_fuel CP) (Z.to_nat (Z.log2_up s))
        |}.

  Ltac get_fill_CurveParameters CP :=
    let CP := (eval hnf in CP) in
    let v := (eval cbv [fill_defaults_CurveParameters] in
                 (fill_defaults_CurveParameters CP)) in
    let v := (eval cbv_CurveParameters in v) in
    let v := (eval cbv_RawCurveParameters in v) in
    lazymatch v with
    | ({|
          sz := ?sz';
          base := ?base';
          bitwidth := ?bitwidth';
          s := ?s';
          c := ?c';
          carry_chains := ?carry_chains';
          a24 := ?a24';
          coef_div_modulus := ?coef_div_modulus';
          goldilocks := ?goldilocks';
          karatsuba := ?karatsuba';
          montgomery := ?montgomery';
          freeze := ?freeze';
          mul_code := ?mul_code';
          square_code := ?square_code';
          upper_bound_of_exponent_tight := ?upper_bound_of_exponent_tight';
          upper_bound_of_exponent_loose := ?upper_bound_of_exponent_loose';
          allowable_bit_widths := ?allowable_bit_widths';
          freeze_allowable_bit_widths := ?freeze_allowable_bit_widths';
          modinv_fuel := ?modinv_fuel'
        |})
      => let sz' := do_compute sz' in
         let base' := do_compute base' in
         let bitwidth' := do_compute bitwidth' in
         let carry_chains' := do_compute carry_chains' in
         let goldilocks' := do_compute goldilocks' in
         let karatsuba' := do_compute karatsuba' in
         let montgomery' := do_compute montgomery' in
         let freeze' := do_compute freeze' in
         let allowable_bit_widths' := do_compute allowable_bit_widths' in
         let freeze_allowable_bit_widths' := do_compute freeze_allowable_bit_widths' in
         let modinv_fuel' := do_compute modinv_fuel' in
         constr:({|
                    sz := sz';
                    base := base';
                    bitwidth := bitwidth';
                    s := s';
                    c := c';
                    carry_chains := carry_chains';
                    a24 := a24';
                    coef_div_modulus := coef_div_modulus';
                    goldilocks := goldilocks';
                    karatsuba := karatsuba';
                    montgomery := montgomery';
                    freeze := freeze';
                    mul_code := mul_code';
                    square_code := square_code';
                    upper_bound_of_exponent_tight := upper_bound_of_exponent_tight';
                    upper_bound_of_exponent_loose := upper_bound_of_exponent_loose';
                    allowable_bit_widths := allowable_bit_widths';
                    freeze_allowable_bit_widths := freeze_allowable_bit_widths';
                    modinv_fuel := modinv_fuel'
                  |})
    end.
  Notation fill_CurveParameters CP := ltac:(let v := get_fill_CurveParameters CP in exact v) (only parsing).
End CurveParameters.
