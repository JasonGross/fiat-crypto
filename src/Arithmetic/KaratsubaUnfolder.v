Require Import Crypto.Arithmetic.CoreUnfolder.
Require Import Crypto.Arithmetic.Karatsuba.

(**
<<
#!/bin/bash
for i in karatsuba_mul_cps karatsuba_mul goldilocks_mul_cps goldilocks_mul; do
    echo "Definition ${i}_sig := parameterize_sig (@${i}).";
    echo "Definition ${i} := parameterize_from_sig ${i}_sig.";
    echo "Definition ${i}_eq := parameterize_eq ${i} ${i}_sig.";
    echo "Hint Unfold ${i} : basesystem_partial_evaluation_unfolder.";
    echo "Hint Rewrite <- ${i}_eq : pattern_runtime."; echo "";
done
>> *)
Definition karatsuba_mul_cps_sig := parameterize_sig (@karatsuba_mul_cps).
Definition karatsuba_mul_cps := parameterize_from_sig karatsuba_mul_cps_sig.
Definition karatsuba_mul_cps_eq := parameterize_eq karatsuba_mul_cps karatsuba_mul_cps_sig.
Hint Unfold karatsuba_mul_cps : basesystem_partial_evaluation_unfolder.
Hint Rewrite <- karatsuba_mul_cps_eq : pattern_runtime.

Definition karatsuba_mul_sig := parameterize_sig (@karatsuba_mul).
Definition karatsuba_mul := parameterize_from_sig karatsuba_mul_sig.
Definition karatsuba_mul_eq := parameterize_eq karatsuba_mul karatsuba_mul_sig.
Hint Unfold karatsuba_mul : basesystem_partial_evaluation_unfolder.
Hint Rewrite <- karatsuba_mul_eq : pattern_runtime.

Definition goldilocks_mul_cps_sig := parameterize_sig (@goldilocks_mul_cps).
Definition goldilocks_mul_cps := parameterize_from_sig goldilocks_mul_cps_sig.
Definition goldilocks_mul_cps_eq := parameterize_eq goldilocks_mul_cps goldilocks_mul_cps_sig.
Hint Unfold goldilocks_mul_cps : basesystem_partial_evaluation_unfolder.
Hint Rewrite <- goldilocks_mul_cps_eq : pattern_runtime.

Definition goldilocks_mul_sig := parameterize_sig (@goldilocks_mul).
Definition goldilocks_mul := parameterize_from_sig goldilocks_mul_sig.
Definition goldilocks_mul_eq := parameterize_eq goldilocks_mul goldilocks_mul_sig.
Hint Unfold goldilocks_mul : basesystem_partial_evaluation_unfolder.
Hint Rewrite <- goldilocks_mul_eq : pattern_runtime.
