theory Core_Preorder_Alignment
  imports "../core_preorder_quotient/Core_Preorder_Quotient"
begin

lemmas preorder_pullback = Core_Preorder_Quotient.preorder_pullback
lemma source_induced_preorder:
  fixes recover :: "'a \<Rightarrow> 't::preorder"
  shows "pre_on A (pullback recover (\<le>))"
  unfolding pre_on_def pullback_def by (auto intro: order_trans)
lemmas quotient_on_representatives = Core_Preorder_Quotient.quotient_on_representatives
lemmas quotient_preorder = Core_Preorder_Quotient.quotient_preorder
lemmas quotient_partial_order = Core_Preorder_Quotient.quotient_partial_order
lemmas quotient_relation_unique = Core_Preorder_Quotient.quotient_relation_unique
lemmas descent_is_necessary = Core_Preorder_Quotient.descent_is_necessary
lemmas empty_quotient = Core_Preorder_Quotient.empty_quotient
lemmas missing_descent_counterexample = Core_Preorder_Quotient.missing_descent_counterexample
lemmas missing_separation_counterexample = Core_Preorder_Quotient.missing_separation_counterexample

ML \<open>
val roots = @{thms preorder_pullback source_induced_preorder quotient_on_representatives quotient_preorder quotient_partial_order quotient_relation_unique descent_is_necessary empty_quotient missing_descent_counterexample missing_separation_counterexample};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
