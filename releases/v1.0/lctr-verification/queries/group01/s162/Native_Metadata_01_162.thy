theory Native_Metadata_01_162
imports
  "LCTR_Generic_Value_Jet_Alignment.Generic_Value_Jet_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Generic_Value_Jet_Alignment.domain_realization",
  "Generic_Value_Jet_Alignment.empty_value_chart_control",
  "Generic_Value_Jet_Alignment.jetAt_eventual_eq",
  "Generic_Value_Jet_Alignment.lift_bijective",
  "Generic_Value_Jet_Alignment.lift_composition",
  "Generic_Value_Jet_Alignment.lift_identity",
  "Generic_Value_Jet_Alignment.lift_left_inverse",
  "Generic_Value_Jet_Alignment.lift_unique",
  "Generic_Value_Jet_Alignment.relation_image",
  "Generic_Value_Jet_Alignment.value_jet_relation_image"
]\<close>
end
