theory Native_Metadata_01_134
imports
  "LCTR_Core_Remaining_Sets.Core_Remaining_Sets"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Remaining_Sets.full_refinement_contract",
  "Core_Remaining_Sets.native_arrival_cover",
  "Core_Remaining_Sets.native_arrival_disjoint"
]\<close>
end
