Require Import Crypto.Arithmetic.CoreUnfolder.
Require Import Crypto.Arithmetic.Saturated.CoreUnfolder.
Require Import Crypto.Arithmetic.Saturated.AddSub.

Module B.
  Module Positional.
  (**
<<
#!/bin/bash
for i in "chain_op'_cps" "chain_op'" chain_op_cps chain_op sat_add_cps sat_add sat_sub_cps sat_sub; do
    echo "    Definition ${i}_sig := parameterize_sig (@B.Positional.${i}).";
    echo "    Definition ${i} := parameterize_from_sig ${i}_sig.";
    echo "    Definition ${i}_eq := parameterize_eq ${i} ${i}_sig.";
    echo "    Hint Unfold ${i} : basesystem_partial_evaluation_unfolder.";
    echo "    Hint Rewrite <- ${i}_eq : pattern_runtime."; echo "";
done
echo "  End Positional."
echo "End B."
>> *)
    Definition chain_op'_cps_sig := parameterize_sig (@B.Positional.chain_op'_cps).
    Definition chain_op'_cps := parameterize_from_sig chain_op'_cps_sig.
    Definition chain_op'_cps_eq := parameterize_eq chain_op'_cps chain_op'_cps_sig.
    Hint Unfold chain_op'_cps : basesystem_partial_evaluation_unfolder.
    Hint Rewrite <- chain_op'_cps_eq : pattern_runtime.

    Definition chain_op'_sig := parameterize_sig (@B.Positional.chain_op').
    Definition chain_op' := parameterize_from_sig chain_op'_sig.
    Definition chain_op'_eq := parameterize_eq chain_op' chain_op'_sig.
    Hint Unfold chain_op' : basesystem_partial_evaluation_unfolder.
    Hint Rewrite <- chain_op'_eq : pattern_runtime.

    Definition chain_op_cps_sig := parameterize_sig (@B.Positional.chain_op_cps).
    Definition chain_op_cps := parameterize_from_sig chain_op_cps_sig.
    Definition chain_op_cps_eq := parameterize_eq chain_op_cps chain_op_cps_sig.
    Hint Unfold chain_op_cps : basesystem_partial_evaluation_unfolder.
    Hint Rewrite <- chain_op_cps_eq : pattern_runtime.

    Definition chain_op_sig := parameterize_sig (@B.Positional.chain_op).
    Definition chain_op := parameterize_from_sig chain_op_sig.
    Definition chain_op_eq := parameterize_eq chain_op chain_op_sig.
    Hint Unfold chain_op : basesystem_partial_evaluation_unfolder.
    Hint Rewrite <- chain_op_eq : pattern_runtime.

    Definition sat_add_cps_sig := parameterize_sig (@B.Positional.sat_add_cps).
    Definition sat_add_cps := parameterize_from_sig sat_add_cps_sig.
    Definition sat_add_cps_eq := parameterize_eq sat_add_cps sat_add_cps_sig.
    Hint Unfold sat_add_cps : basesystem_partial_evaluation_unfolder.
    Hint Rewrite <- sat_add_cps_eq : pattern_runtime.

    Definition sat_add_sig := parameterize_sig (@B.Positional.sat_add).
    Definition sat_add := parameterize_from_sig sat_add_sig.
    Definition sat_add_eq := parameterize_eq sat_add sat_add_sig.
    Hint Unfold sat_add : basesystem_partial_evaluation_unfolder.
    Hint Rewrite <- sat_add_eq : pattern_runtime.

    Definition sat_sub_cps_sig := parameterize_sig (@B.Positional.sat_sub_cps).
    Definition sat_sub_cps := parameterize_from_sig sat_sub_cps_sig.
    Definition sat_sub_cps_eq := parameterize_eq sat_sub_cps sat_sub_cps_sig.
    Hint Unfold sat_sub_cps : basesystem_partial_evaluation_unfolder.
    Hint Rewrite <- sat_sub_cps_eq : pattern_runtime.

    Definition sat_sub_sig := parameterize_sig (@B.Positional.sat_sub).
    Definition sat_sub := parameterize_from_sig sat_sub_sig.
    Definition sat_sub_eq := parameterize_eq sat_sub sat_sub_sig.
    Hint Unfold sat_sub : basesystem_partial_evaluation_unfolder.
    Hint Rewrite <- sat_sub_eq : pattern_runtime.

  End Positional.
End B.
