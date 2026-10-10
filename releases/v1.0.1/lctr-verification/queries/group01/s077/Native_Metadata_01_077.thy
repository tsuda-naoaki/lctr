theory Native_Metadata_01_077
imports
  "LCTR_Core_Law_Datum_Assembly.Core_Law_Datum_Assembly"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Law_Datum_Assembly.common_valid_contract",
  "Core_Law_Datum_Assembly.component_projection",
  "Core_Law_Datum_Assembly.coupling_joint",
  "Core_Law_Datum_Assembly.coupling_single",
  "Core_Law_Datum_Assembly.evaluation_tuple_domain_typed",
  "Core_Law_Datum_Assembly.evaluation_tuple_projections",
  "Core_Law_Datum_Assembly.family_projections",
  "Core_Law_Datum_Assembly.individual_input_typed",
  "Core_Law_Datum_Assembly.native_law_context.native_component_projection",
  "Core_Law_Datum_Assembly.outer_projections"
]\<close>
end
