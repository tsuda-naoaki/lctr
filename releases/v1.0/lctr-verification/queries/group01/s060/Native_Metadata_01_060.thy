theory Native_Metadata_01_060
imports
  "LCTR_Core_Finite_Report_Components.Core_Finite_Report_Components"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Finite_Report_Components.burden_exact",
  "Core_Finite_Report_Components.burden_from_singleton_images",
  "Core_Finite_Report_Components.fiber_exact",
  "Core_Finite_Report_Components.local_reasons_exact",
  "Core_Finite_Report_Components.reasons_exact",
  "Core_Finite_Report_Components.tagged_exact",
  "Core_Finite_Report_Components.tagged_has_nonempty_reason"
]\<close>
end
