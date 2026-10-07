theory Core_Continuum_Topology_Alignment
  imports LCTR_Core_Continuum_Topology.Core_Continuum_Topology
begin
lemmas positive_domain_open = Core_Continuum_Topology.positive_domain_open
lemmas open_neighborhood_iff = Core_Continuum_Topology.open_neighborhood_iff
lemmas robust_positive_iff = Core_Continuum_Topology.robust_positive_iff
lemmas operational_robust_domain_open = approximation_margin_topology.operational_robust_domain_open
lemmas source_order_topology_neighborhood = approximation_margin_topology.robust_open_neighborhood

lemma missing_input_control:
  "(\<lambda>t. Unformed) = eval_update edges (\<lambda>t. False) (\<lambda>t. True) (\<lambda>t. True) (\<lambda>t. Unformed)
    \<and> (\<forall>i\<in>approx_set. 0<margin 1 0)
    \<and> \<not>operational_robust (\<lambda>t. Unformed) (\<lambda>t. 0) (\<lambda>t. 1)"
  using Core_Continuum_Topology.missing_input_control by blast

ML \<open>
val roots = @{thms positive_domain_open open_neighborhood_iff robust_positive_iff
  operational_robust_domain_open source_order_topology_neighborhood missing_input_control};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
