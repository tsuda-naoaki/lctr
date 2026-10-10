theory Native_Metadata_06_001
imports
  "LCTR_Core_Report_Covariance.Core_Report_Covariance"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Report_Covariance.approximation_group_image",
  "Core_Report_Covariance.assembled_report_transport",
  "Core_Report_Covariance.burden_report_transport",
  "Core_Report_Covariance.diagnostic_report_transport",
  "Core_Report_Covariance.function_transport",
  "Core_Report_Covariance.induced_report_equiv_unique",
  "Core_Report_Covariance.native_output_transport",
  "Core_Report_Covariance.native_report_covariance",
  "Core_Report_Covariance.state_report_transport"
]\<close>
end
