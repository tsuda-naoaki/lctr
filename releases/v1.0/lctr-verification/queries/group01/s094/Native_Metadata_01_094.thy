theory Native_Metadata_01_094
imports
  "LCTR_Core_Native_Curves.Core_Native_Curves"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Native_Curves.observer_linear.restricted_projection_contract",
  "Core_Native_Curves.observer_real.observable_curve_unique_from_canonical",
  "Core_Native_Curves.observer_real.observable_factorization",
  "Core_Native_Curves.observer_real.real_domain_composition",
  "Core_Native_Curves.observer_real.real_image_inverse_contract",
  "Core_Native_Curves.observer_seed.canonical_graph_contract",
  "Core_Native_Curves.observer_seed.empty_source_domain",
  "Core_Native_Curves.observer_seed.scalar_factor_contract",
  "Core_Native_Curves.observer_seed.scalar_factor_exists_unique",
  "Core_Native_Curves.observer_seed.scalar_factor_requires_fiber"
]\<close>
end
