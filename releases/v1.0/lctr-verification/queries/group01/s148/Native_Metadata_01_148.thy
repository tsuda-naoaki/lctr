theory Native_Metadata_01_148
imports
  "LCTR_Core_Structural_Burden.Core_Structural_Burden"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Structural_Burden.boundary_burden_covariance",
  "Core_Structural_Burden.burden_mono",
  "Core_Structural_Burden.burden_separation",
  "Core_Structural_Burden.burden_transport",
  "Core_Structural_Burden.native_burden_covariance",
  "Core_Structural_Burden.native_burden_upward",
  "Core_Structural_Burden.native_failed_burden_covariance",
  "Core_Structural_Burden.native_root_included",
  "Core_Structural_Burden.reach_map",
  "Core_Structural_Burden.reach_transport",
  "Core_Structural_Burden.report_unique",
  "Core_Structural_Burden.root_burden_subset",
  "Core_Structural_Burden.singleton_burden"
]\<close>
end
