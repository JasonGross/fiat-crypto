#!/usr/bin/env python2.7
from __future__ import with_statement

for name, opkind in ([(name, 'BinOp') for name in ('Add', 'Carry_Add', 'Sub', 'Carry_Sub', 'Mul')]
                     + [(name, 'UnOp') for name in ('Opp', 'Carry_Opp', 'PreFreeze')]
                     + [('Ge_Modulus', 'UnOp_FEToZ'), ('Pack', 'UnOp_FEToWire'), ('Unpack', 'UnOp_WireToFE')]):
    lname = name.lower()
    lopkind = opkind.replace('UnOp', 'unop').replace('BinOp', 'binop')
    uopkind = opkind.replace('_', '')
    extra = ''
    #if name in ('Carry_Add', 'Carry_Sub', 'Mul', 'Carry_Opp', 'Pack', 'Unpack', 'Ge_Modulus', 'PreFreeze'):
    extra = r"""Local Obligation Tactic := rexpr_correct_and_bounded_obligation_tac.
Program Definition r%(lname)sZ_correct_and_bounded_tight
  : rexpr_correct_and_boundedT r%(lname)sZ r%(lname)sW Expr%(uopkind)s_bounds r%(lname)s_output_bounds
  := rexpr_correct_and_bounded r%(lname)sZ r%(lname)sW Expr%(uopkind)s_bounds r%(lname)s_output_bounds r%(lname)sZ_Wf.
""" % locals()
    with open(name.replace('_', '') + '.v', 'w') as f:
        f.write(r"""Require Import Crypto.Specific.GF25519Reflective.Common.

Definition r%(lname)sZ_sig : rexpr_%(lopkind)s_sig %(lname)s. Proof. reify_sig. Defined.
Definition r%(lname)sZ : Expr _ := Eval vm_compute in proj1_sig r%(lname)sZ_sig.
Definition r%(lname)sW_pkgo := Eval vm_compute in rexpr_select_word_sizes_option r%(lname)sZ Expr%(uopkind)s_bounds.
Definition r%(lname)sW_pkg := Eval vm_compute in rexpr_select_word_sizes_postprocess1 r%(lname)sW_pkgo.
Definition r%(lname)sT := get_output_type r%(lname)sW_pkg.
Definition r%(lname)sW' : Expr _ := Eval vm_compute in get_output_expr r%(lname)sW_pkg.
Definition r%(lname)sW : Expr r%(lname)sT := Eval cbv [r%(lname)sW'] in rexpr_select_word_sizes_postprocess2 r%(lname)sW'.
Definition r%(lname)s_output_bounds := Eval vm_compute in get_bounds r%(lname)sW_pkg.
Definition r%(lname)sZ_Wf : rexpr_wfT r%(lname)sZ. Proof. prove_rexpr_wfT. Qed.
%(extra)s
Local Open Scope string_scope.
Compute ("%(name)s", compute_bounds_for_display r%(lname)sW_pkg).
(* We use [compute] rather than [vm_compute] so as to not eta-expand functions, so we get pretty display *)
Eval compute in ("%(name)s overflows? ", sanity_compute r%(lname)sW_pkg).
Compute ("%(name)s overflows (error if it does)? ", sanity_check r%(lname)sW_pkg).
""" % locals())
