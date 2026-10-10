theory Native_Metadata_01_108
imports
  "LCTR_Core_Nonmonotone_Boundary_Data.Core_Nonmonotone_Boundary_Data"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Nonmonotone_Boundary_Data.envelope_dominates",
  "Core_Nonmonotone_Boundary_Data.envelope_least",
  "Core_Nonmonotone_Boundary_Data.envelope_member_bound",
  "Core_Nonmonotone_Boundary_Data.envelope_method_permission",
  "Core_Nonmonotone_Boundary_Data.envelope_monotone",
  "Core_Nonmonotone_Boundary_Data.finite_envelope_defects_finite",
  "Core_Nonmonotone_Boundary_Data.finite_envelope_exact",
  "Core_Nonmonotone_Boundary_Data.infinite_defect_no_finite_envelope",
  "Core_Nonmonotone_Boundary_Data.no_priority_when_both",
  "Core_Nonmonotone_Boundary_Data.partition_cover",
  "Core_Nonmonotone_Boundary_Data.partition_method_permission",
  "Core_Nonmonotone_Boundary_Data.partition_monotone",
  "Core_Nonmonotone_Boundary_Data.partition_order_convex",
  "Core_Nonmonotone_Boundary_Data.partition_unique",
  "Core_Nonmonotone_Boundary_Data.unformed_when_neither"
]\<close>
end
