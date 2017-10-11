Require Import Coq.ZArith.ZArith Coq.ZArith.BinIntDef.
Require Import Crypto.Arithmetic.Core. Import B.
Require Import Crypto.Util.ZUtil.ModInv.
Require Crypto.Util.Tuple.

Local Notation tuple := Tuple.tuple.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Ltac if_cond_else cond tac default id :=
  lazymatch (eval compute in cond) with
  | true => tac id
  | false => default
  end.
Ltac if_cond cond tac id := if_cond_else cond tac (0%Z) id.

Ltac solve_modinv modinv_fuel a modulus :=
  let v := constr:(Option.invert_Some (Z.modinv_fueled modinv_fuel a modulus)) in
  let v := (eval vm_compute in v) in
  let v := (eval vm_compute in (v : Z)) in
  exact v.

Ltac pose_proof_tuple ls :=
  lazymatch ls with
  | pair ?x ?y => pose_proof_tuple x; pose_proof_tuple y
  | ?ls
    => let t := type of ls in
       lazymatch (eval hnf in t) with
       | prod _ _
         => pose_proof_tuple (fst ls); pose_proof_tuple (snd ls)
       | _ => pose proof ls
       end
  end.

Ltac make_chained_carries_cps' sz wt s c a carry_chains :=
  lazymatch carry_chains with
  | ?carry_chain :: nil
    => constr:(Positional.chained_carries_cps (n:=sz) (div:=div) (modulo:=modulo) wt a carry_chain id)
  | ?carry_chain :: ?carry_chains
    => let r := fresh "r" in
       let r' := fresh r in
       constr:(Positional.chained_carries_cps (n:=sz) (div:=div) (modulo:=modulo) wt a carry_chain
                                              (fun r => Positional.carry_reduce_cps (n:=sz) (div:=div) (modulo:=modulo) wt s c r
                                                                                    (fun r' => ltac:(let v := make_chained_carries_cps' sz wt s c r' carry_chains in exact v))))
  end.
Ltac make_chained_carries_cps sz wt s c a carry_chains :=
  let carry_chains := (eval cbv delta [carry_chains] in carry_chains) in
  make_chained_carries_cps' sz wt s c a carry_chains.
