theory Native_Metadata_01_021
imports
  "LCTR_Core_Continuum_Boundary_Alignment.Core_Continuum_Boundary_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Continuum_Boundary_Alignment.excess_nonneg",
  "Core_Continuum_Boundary_Alignment.excess_positive",
  "Core_Continuum_Boundary_Alignment.excess_zero",
  "Core_Continuum_Boundary_Alignment.first_excess",
  "Core_Continuum_Boundary_Alignment.first_excess_is_least",
  "Core_Continuum_Boundary_Alignment.infinite_saturation_control",
  "Core_Continuum_Boundary_Alignment.initial_boundary",
  "Core_Continuum_Boundary_Alignment.least_subset",
  "Core_Continuum_Boundary_Alignment.margin_negative",
  "Core_Continuum_Boundary_Alignment.margin_nonneg",
  "Core_Continuum_Boundary_Alignment.margin_positive",
  "Core_Continuum_Boundary_Alignment.margin_zero",
  "Core_Continuum_Boundary_Alignment.maximal_effective_interval",
  "Core_Continuum_Boundary_Alignment.maximal_initial_eq",
  "Core_Continuum_Boundary_Alignment.maximal_initial_greatest",
  "Core_Continuum_Boundary_Alignment.maximum_has_no_excess",
  "Core_Continuum_Boundary_Alignment.monotone_defects_initial",
  "Core_Continuum_Boundary_Alignment.no_least_open_excess_control",
  "Core_Continuum_Boundary_Alignment.saturation_excess_disjoint",
  "Core_Continuum_Boundary_Alignment.subset_excess",
  "Core_Continuum_Boundary_Alignment.subset_saturation",
  "Core_Continuum_Boundary_Alignment.valid_not_robust",
  "Core_Continuum_Boundary_Alignment.validity_characterizations"
]\<close>
end
