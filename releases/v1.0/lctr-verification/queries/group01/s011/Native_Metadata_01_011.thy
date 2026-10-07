theory Native_Metadata_01_011
imports
  "LCTR_Core_Comparison_Definition_Interfaces.Core_Comparison_Definition_Interfaces"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Comparison_Definition_Interfaces.failed_exact",
  "Core_Comparison_Definition_Interfaces.failed_token_membership",
  "Core_Comparison_Definition_Interfaces.failure_domain_partition",
  "Core_Comparison_Definition_Interfaces.first_prefix_empty",
  "Core_Comparison_Definition_Interfaces.indicator_false",
  "Core_Comparison_Definition_Interfaces.indicator_true",
  "Core_Comparison_Definition_Interfaces.membership_indicator",
  "Core_Comparison_Definition_Interfaces.raw_exact",
  "Core_Comparison_Definition_Interfaces.raw_gluing",
  "Core_Comparison_Definition_Interfaces.raw_local",
  "Core_Comparison_Definition_Interfaces.readiness",
  "Core_Comparison_Definition_Interfaces.signature_binary",
  "Core_Comparison_Definition_Interfaces.signature_indicator"
]\<close>
end
