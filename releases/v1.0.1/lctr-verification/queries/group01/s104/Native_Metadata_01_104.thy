theory Native_Metadata_01_104
imports
  "LCTR_Core_Native_Specification.Core_Native_Specification"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Native_Specification.approximate_restriction_identity",
  "Core_Native_Specification.approximate_specification",
  "Core_Native_Specification.approximation_to_strict_projection",
  "Core_Native_Specification.edge_kind",
  "Core_Native_Specification.empty_scale_uniqueness_control",
  "Core_Native_Specification.evaluation_exact",
  "Core_Native_Specification.predecessor_section_coherent",
  "Core_Native_Specification.restriction_coherent",
  "Core_Native_Specification.restriction_unique_on_image",
  "Core_Native_Specification.strict_restriction_identity",
  "Core_Native_Specification.strict_restriction_unique_with_scale",
  "Core_Native_Specification.strict_scale_independent",
  "Core_Native_Specification.strict_specification",
  "Core_Native_Specification.totalization_off_domain",
  "Core_Native_Specification.totalization_on_domain",
  "Core_Native_Specification.totalization_original_exists"
]\<close>
end
