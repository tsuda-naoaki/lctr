theory Native_Metadata_10_001
imports
  "LCTR_Core_Engineering_Input_Burden.Core_Engineering_Input_Burden"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Engineering_Input_Burden.all_references_typed",
  "Core_Engineering_Input_Burden.bulk_tags_exact",
  "Core_Engineering_Input_Burden.burden_exact",
  "Core_Engineering_Input_Burden.communication_origin",
  "Core_Engineering_Input_Burden.config_origin",
  "Core_Engineering_Input_Burden.configuration_delta",
  "Core_Engineering_Input_Burden.evidence_exact",
  "Core_Engineering_Input_Burden.failed_exact",
  "Core_Engineering_Input_Burden.following_tags_exact",
  "Core_Engineering_Input_Burden.four_other_tags_excluded",
  "Core_Engineering_Input_Burden.indexed_exact",
  "Core_Engineering_Input_Burden.indexed_separates",
  "Core_Engineering_Input_Burden.invasion_origin",
  "Core_Engineering_Input_Burden.nonfail_excluded",
  "Core_Engineering_Input_Burden.outside_tags_excluded",
  "Core_Engineering_Input_Burden.range_not_ambient",
  "Core_Engineering_Input_Burden.tag_complete",
  "Core_Engineering_Input_Burden.tag_count",
  "Core_Engineering_Input_Burden.tag_distinct",
  "Core_Engineering_Input_Burden.tokens_exact",
  "Core_Engineering_Input_Burden.union_exact",
  "Core_Engineering_Input_Burden.view_origin"
]\<close>
end
