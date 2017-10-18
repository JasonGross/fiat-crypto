Require Import Crypto.Arithmetic.CoreUnfolder.
Require Import Crypto.Arithmetic.Saturated.CoreUnfolder.
Require Import Crypto.Arithmetic.Saturated.WrappersUnfolder.
Require Import Crypto.Arithmetic.Saturated.AddSubUnfolder.
Require Import Crypto.Arithmetic.Saturated.MontgomeryAPI.
Require Import Crypto.Arithmetic.Saturated.MontgomeryAPI.

Module MontgomeryAPI.
  (**
<<
#!/bin/bash
for i in zero nonzero_cps nonzero join0_cps join0 divmod_cps divmod drop_high_cps drop_high scmul_cps scmul add_cps add add_S1_cps add_S1 add_S2_cps add_S2 sub_then_maybe_add_cps sub_then_maybe_add conditional_sub_cps conditional_sub eval compact compact_digit; do
    echo "  Definition ${i}_sig := parameterize_sig (@MontgomeryAPI.${i}).";
    echo "  Definition ${i} := parameterize_from_sig ${i}_sig.";
    echo "  Definition ${i}_eq := parameterize_eq ${i} ${i}_sig.";
    echo "  Hint Unfold ${i} : basesystem_partial_evaluation_unfolder.";
    echo "  Hint Rewrite <- ${i}_eq : pattern_runtime."; echo "";
done
echo "End MontgomeryAPI."
>> *)
  Definition zero_sig := parameterize_sig (@MontgomeryAPI.zero).
  Definition zero := parameterize_from_sig zero_sig.
  Definition zero_eq := parameterize_eq zero zero_sig.
  Hint Unfold zero : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- zero_eq : pattern_runtime.

  Definition nonzero_cps_sig := parameterize_sig (@MontgomeryAPI.nonzero_cps).
  Definition nonzero_cps := parameterize_from_sig nonzero_cps_sig.
  Definition nonzero_cps_eq := parameterize_eq nonzero_cps nonzero_cps_sig.
  Hint Unfold nonzero_cps : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- nonzero_cps_eq : pattern_runtime.

  Definition nonzero_sig := parameterize_sig (@MontgomeryAPI.nonzero).
  Definition nonzero := parameterize_from_sig nonzero_sig.
  Definition nonzero_eq := parameterize_eq nonzero nonzero_sig.
  Hint Unfold nonzero : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- nonzero_eq : pattern_runtime.

  Definition join0_cps_sig := parameterize_sig (@MontgomeryAPI.join0_cps).
  Definition join0_cps := parameterize_from_sig join0_cps_sig.
  Definition join0_cps_eq := parameterize_eq join0_cps join0_cps_sig.
  Hint Unfold join0_cps : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- join0_cps_eq : pattern_runtime.

  Definition join0_sig := parameterize_sig (@MontgomeryAPI.join0).
  Definition join0 := parameterize_from_sig join0_sig.
  Definition join0_eq := parameterize_eq join0 join0_sig.
  Hint Unfold join0 : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- join0_eq : pattern_runtime.

  Definition divmod_cps_sig := parameterize_sig (@MontgomeryAPI.divmod_cps).
  Definition divmod_cps := parameterize_from_sig divmod_cps_sig.
  Definition divmod_cps_eq := parameterize_eq divmod_cps divmod_cps_sig.
  Hint Unfold divmod_cps : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- divmod_cps_eq : pattern_runtime.

  Definition divmod_sig := parameterize_sig (@MontgomeryAPI.divmod).
  Definition divmod := parameterize_from_sig divmod_sig.
  Definition divmod_eq := parameterize_eq divmod divmod_sig.
  Hint Unfold divmod : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- divmod_eq : pattern_runtime.

  Definition drop_high_cps_sig := parameterize_sig (@MontgomeryAPI.drop_high_cps).
  Definition drop_high_cps := parameterize_from_sig drop_high_cps_sig.
  Definition drop_high_cps_eq := parameterize_eq drop_high_cps drop_high_cps_sig.
  Hint Unfold drop_high_cps : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- drop_high_cps_eq : pattern_runtime.

  Definition drop_high_sig := parameterize_sig (@MontgomeryAPI.drop_high).
  Definition drop_high := parameterize_from_sig drop_high_sig.
  Definition drop_high_eq := parameterize_eq drop_high drop_high_sig.
  Hint Unfold drop_high : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- drop_high_eq : pattern_runtime.

  Definition scmul_cps_sig := parameterize_sig (@MontgomeryAPI.scmul_cps).
  Definition scmul_cps := parameterize_from_sig scmul_cps_sig.
  Definition scmul_cps_eq := parameterize_eq scmul_cps scmul_cps_sig.
  Hint Unfold scmul_cps : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- scmul_cps_eq : pattern_runtime.

  Definition scmul_sig := parameterize_sig (@MontgomeryAPI.scmul).
  Definition scmul := parameterize_from_sig scmul_sig.
  Definition scmul_eq := parameterize_eq scmul scmul_sig.
  Hint Unfold scmul : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- scmul_eq : pattern_runtime.

  Definition add_cps_sig := parameterize_sig (@MontgomeryAPI.add_cps).
  Definition add_cps := parameterize_from_sig add_cps_sig.
  Definition add_cps_eq := parameterize_eq add_cps add_cps_sig.
  Hint Unfold add_cps : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- add_cps_eq : pattern_runtime.

  Definition add_sig := parameterize_sig (@MontgomeryAPI.add).
  Definition add := parameterize_from_sig add_sig.
  Definition add_eq := parameterize_eq add add_sig.
  Hint Unfold add : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- add_eq : pattern_runtime.

  Definition add_S1_cps_sig := parameterize_sig (@MontgomeryAPI.add_S1_cps).
  Definition add_S1_cps := parameterize_from_sig add_S1_cps_sig.
  Definition add_S1_cps_eq := parameterize_eq add_S1_cps add_S1_cps_sig.
  Hint Unfold add_S1_cps : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- add_S1_cps_eq : pattern_runtime.

  Definition add_S1_sig := parameterize_sig (@MontgomeryAPI.add_S1).
  Definition add_S1 := parameterize_from_sig add_S1_sig.
  Definition add_S1_eq := parameterize_eq add_S1 add_S1_sig.
  Hint Unfold add_S1 : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- add_S1_eq : pattern_runtime.

  Definition add_S2_cps_sig := parameterize_sig (@MontgomeryAPI.add_S2_cps).
  Definition add_S2_cps := parameterize_from_sig add_S2_cps_sig.
  Definition add_S2_cps_eq := parameterize_eq add_S2_cps add_S2_cps_sig.
  Hint Unfold add_S2_cps : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- add_S2_cps_eq : pattern_runtime.

  Definition add_S2_sig := parameterize_sig (@MontgomeryAPI.add_S2).
  Definition add_S2 := parameterize_from_sig add_S2_sig.
  Definition add_S2_eq := parameterize_eq add_S2 add_S2_sig.
  Hint Unfold add_S2 : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- add_S2_eq : pattern_runtime.

  Definition sub_then_maybe_add_cps_sig := parameterize_sig (@MontgomeryAPI.sub_then_maybe_add_cps).
  Definition sub_then_maybe_add_cps := parameterize_from_sig sub_then_maybe_add_cps_sig.
  Definition sub_then_maybe_add_cps_eq := parameterize_eq sub_then_maybe_add_cps sub_then_maybe_add_cps_sig.
  Hint Unfold sub_then_maybe_add_cps : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- sub_then_maybe_add_cps_eq : pattern_runtime.

  Definition sub_then_maybe_add_sig := parameterize_sig (@MontgomeryAPI.sub_then_maybe_add).
  Definition sub_then_maybe_add := parameterize_from_sig sub_then_maybe_add_sig.
  Definition sub_then_maybe_add_eq := parameterize_eq sub_then_maybe_add sub_then_maybe_add_sig.
  Hint Unfold sub_then_maybe_add : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- sub_then_maybe_add_eq : pattern_runtime.

  Definition conditional_sub_cps_sig := parameterize_sig (@MontgomeryAPI.conditional_sub_cps).
  Definition conditional_sub_cps := parameterize_from_sig conditional_sub_cps_sig.
  Definition conditional_sub_cps_eq := parameterize_eq conditional_sub_cps conditional_sub_cps_sig.
  Hint Unfold conditional_sub_cps : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- conditional_sub_cps_eq : pattern_runtime.

  Definition conditional_sub_sig := parameterize_sig (@MontgomeryAPI.conditional_sub).
  Definition conditional_sub := parameterize_from_sig conditional_sub_sig.
  Definition conditional_sub_eq := parameterize_eq conditional_sub conditional_sub_sig.
  Hint Unfold conditional_sub : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- conditional_sub_eq : pattern_runtime.

  Definition eval_sig := parameterize_sig (@MontgomeryAPI.eval).
  Definition eval := parameterize_from_sig eval_sig.
  Definition eval_eq := parameterize_eq eval eval_sig.
  Hint Unfold eval : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- eval_eq : pattern_runtime.

  Definition compact_sig := parameterize_sig (@MontgomeryAPI.compact).
  Definition compact := parameterize_from_sig compact_sig.
  Definition compact_eq := parameterize_eq compact compact_sig.
  Hint Unfold compact : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- compact_eq : pattern_runtime.

  Definition compact_digit_sig := parameterize_sig (@MontgomeryAPI.compact_digit).
  Definition compact_digit := parameterize_from_sig compact_digit_sig.
  Definition compact_digit_eq := parameterize_eq compact_digit compact_digit_sig.
  Hint Unfold compact_digit : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- compact_digit_eq : pattern_runtime.

End MontgomeryAPI.
