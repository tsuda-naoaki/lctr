theory Native_Metadata_01_081
imports
  "LCTR_Core_Law_Input_Bundle.Core_Law_Input_Bundle"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Law_Input_Bundle.native_law_bundle.law_input_exists_unique",
  "Core_Law_Input_Bundle.native_law_bundle.law_input_spec",
  "Core_Law_Input_Bundle.native_law_bundle.law_input_unique",
  "Core_Law_Input_Bundle.native_law_bundle.observable_change_preserved",
  "Core_Law_Input_Bundle.native_law_bundle.observable_spec",
  "Core_Law_Input_Bundle.native_law_bundle.observable_unique",
  "Core_Law_Input_Bundle.native_law_bundle.observable_value_typed",
  "Core_Law_Input_Bundle.native_law_bundle.record_pair_typed",
  "Core_Law_Input_Bundle.native_law_bundle.role_record_projection",
  "Core_Law_Input_Bundle.native_law_bundle.source_relation_exact"
]\<close>
end
