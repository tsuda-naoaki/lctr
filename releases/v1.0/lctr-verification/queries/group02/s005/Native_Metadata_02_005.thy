theory Native_Metadata_02_005
imports
  "LCTR_Core_Source_Match_Alignment.Core_Source_Match_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Source_Match_Alignment.arrival_recovery",
  "Core_Source_Match_Alignment.equal_display_not_source_match",
  "Core_Source_Match_Alignment.equal_recovery_orbit",
  "Core_Source_Match_Alignment.l1_iff_injective",
  "Core_Source_Match_Alignment.mutual_arrival_order_separation",
  "Core_Source_Match_Alignment.recover_srcMatch",
  "Core_Source_Match_Alignment.recovery_injective",
  "Core_Source_Match_Alignment.same_source_native_match",
  "Core_Source_Match_Alignment.sourceWord_action",
  "Core_Source_Match_Alignment.sourceWord_encoding",
  "Core_Source_Match_Alignment.source_match_functional",
  "Core_Source_Match_Alignment.source_match_injective",
  "Core_Source_Match_Alignment.source_match_inverse_graph",
  "Core_Source_Match_Alignment.srcGraph_iff_same_recovery"
]\<close>
end
