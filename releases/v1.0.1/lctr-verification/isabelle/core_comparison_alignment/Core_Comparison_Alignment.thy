theory Core_Comparison_Alignment
  imports LCTR_Core_Comparison_Integration.Core_Comparison_Integration
begin
lemmas comparison_equivalence = native_comparison.comparison_equivalence
lemmas equal_recovery_comparison = native_comparison.equal_recovery_comparison
lemmas comparison_order_separation = native_comparison.comparison_order_separation
lemmas canonical_comparison_partial_order = native_comparison.canonical_comparison_partial_order
lemmas comparison_loop_projection_criterion = native_comparison.comparison_loop_projection_criterion
ML \<open>
val roots = @{thms comparison_equivalence equal_recovery_comparison
  comparison_order_separation canonical_comparison_partial_order comparison_loop_projection_criterion};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
