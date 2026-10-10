theory Native_Metadata_01_074
imports
  "LCTR_Core_Judgment_Boundary.Core_Judgment_Boundary"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Judgment_Boundary.approximation7_extension",
  "Core_Judgment_Boundary.approximation8_order",
  "Core_Judgment_Boundary.approximation9_relation",
  "Core_Judgment_Boundary.approximation_quantitative",
  "Core_Judgment_Boundary.complete_differential_control",
  "Core_Judgment_Boundary.component_bridge_suffices",
  "Core_Judgment_Boundary.differential3_jet_membership",
  "Core_Judgment_Boundary.differential4_value_covariance",
  "Core_Judgment_Boundary.differential5_time_covariance",
  "Core_Judgment_Boundary.incomplete_differential_control",
  "Core_Judgment_Boundary.inconsistent_bridge_rejected",
  "Core_Judgment_Boundary.jet_membership_native_domain",
  "Core_Judgment_Boundary.law3_trajectory_membership",
  "Core_Judgment_Boundary.law4_relation_reexpression",
  "Core_Judgment_Boundary.no_unconditional_transfer",
  "Core_Judgment_Boundary.same_approximation_different_differential_results"
]\<close>
end
