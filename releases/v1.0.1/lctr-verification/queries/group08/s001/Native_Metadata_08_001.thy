theory Native_Metadata_08_001
imports
  "LCTR_Core_Engineering_Data_Interfaces.Core_Engineering_Data_Interfaces"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Engineering_Data_Interfaces.empty_views",
  "Core_Engineering_Data_Interfaces.engineering_components",
  "Core_Engineering_Data_Interfaces.following_exact",
  "Core_Engineering_Data_Interfaces.following_not_bulk",
  "Core_Engineering_Data_Interfaces.infinite_threshold_pass",
  "Core_Engineering_Data_Interfaces.interval_fail",
  "Core_Engineering_Data_Interfaces.interval_indeterminate",
  "Core_Engineering_Data_Interfaces.interval_membership",
  "Core_Engineering_Data_Interfaces.interval_pass",
  "Core_Engineering_Data_Interfaces.interval_range",
  "Core_Engineering_Data_Interfaces.invasiveness_components",
  "Core_Engineering_Data_Interfaces.invasiveness_exact",
  "Core_Engineering_Data_Interfaces.missing_record_excludes_following",
  "Core_Engineering_Data_Interfaces.pair_common_context",
  "Core_Engineering_Data_Interfaces.restricted_domain",
  "Core_Engineering_Data_Interfaces.restricted_relation",
  "Core_Engineering_Data_Interfaces.threshold_equality_pass",
  "Core_Engineering_Data_Interfaces.view_components"
]\<close>
end
