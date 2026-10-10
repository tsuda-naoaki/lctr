theory Native_Metadata_01_086
imports
  "LCTR_Core_Least_Scale_Lift.Core_Least_Scale_Lift"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Least_Scale_Lift.domain_exact",
  "Core_Least_Scale_Lift.empty_fibre_undefined",
  "Core_Least_Scale_Lift.graph_exact",
  "Core_Least_Scale_Lift.graph_singlevalued",
  "Core_Least_Scale_Lift.same_sets_domain",
  "Core_Least_Scale_Lift.same_sets_value",
  "Core_Least_Scale_Lift.value_is_least",
  "Core_Least_Scale_Lift.value_unique"
]\<close>
end
