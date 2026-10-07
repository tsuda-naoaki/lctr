theory Native_Metadata_01_022
imports
  "LCTR_Core_Continuum_Datum.Core_Continuum_Datum"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Continuum_Datum.cell_width_bound",
  "Core_Continuum_Datum.cell_width_excess",
  "Core_Continuum_Datum.collision_witness",
  "Core_Continuum_Datum.condition_true",
  "Core_Continuum_Datum.diameter_bound",
  "Core_Continuum_Datum.diameter_empty",
  "Core_Continuum_Datum.diameter_excess",
  "Core_Continuum_Datum.extension_failure_witness",
  "Core_Continuum_Datum.order_failure_witness",
  "Core_Continuum_Datum.packet_evaluation.actual_failure",
  "Core_Continuum_Datum.packet_evaluation.extension_failure",
  "Core_Continuum_Datum.packet_evaluation.order_failure",
  "Core_Continuum_Datum.packet_evaluation.relation_failure",
  "Core_Continuum_Datum.packet_evaluation.separation_failure",
  "Core_Continuum_Datum.packet_evaluation.unit_separation_tolerance",
  "Core_Continuum_Datum.packet_evaluation.width_failure",
  "Core_Continuum_Datum.packet_evaluation.zero_separation_tolerance",
  "Core_Continuum_Datum.relation_failure_witness",
  "Core_Continuum_Datum.separation_defect_excess",
  "Core_Continuum_Datum.three_record_defects",
  "Core_Continuum_Datum.width_equals_source_supremum"
]\<close>
end
