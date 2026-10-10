theory Native_Metadata_01_115
imports
  "LCTR_Core_Pair_Transport_Factorization.Core_Pair_Transport_Factorization"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Pair_Transport_Factorization.existence_unique_iff",
  "Core_Pair_Transport_Factorization.factorization_unique",
  "Core_Pair_Transport_Factorization.joint_function_does_not_ensure_component_factorization",
  "Core_Pair_Transport_Factorization.pair_factorization.component_functional",
  "Core_Pair_Transport_Factorization.pair_factorization.component_graph_exact",
  "Core_Pair_Transport_Factorization.pair_factorization.component_injective",
  "Core_Pair_Transport_Factorization.pair_factorization.domain_forced"
]\<close>
end
