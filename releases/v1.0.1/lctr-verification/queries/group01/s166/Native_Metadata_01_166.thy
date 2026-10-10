theory Native_Metadata_01_166
imports
  "LCTR_Native_Family_Alignment.Native_Family_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Native_Family_Alignment.between_preserves_native_values",
  "Native_Family_Alignment.native_failure_cover(1)",
  "Native_Family_Alignment.native_failure_cover(2)",
  "Native_Family_Alignment.native_failure_cover(3)",
  "Native_Family_Alignment.native_fifth_condition(1)",
  "Native_Family_Alignment.native_fifth_condition(2)",
  "Native_Family_Alignment.native_fifth_condition(3)",
  "Native_Family_Alignment.native_first_condition(1)",
  "Native_Family_Alignment.native_first_condition(2)",
  "Native_Family_Alignment.native_first_condition(3)",
  "Native_Family_Alignment.native_fourth_condition(1)",
  "Native_Family_Alignment.native_fourth_condition(2)",
  "Native_Family_Alignment.native_fourth_condition(3)",
  "Native_Family_Alignment.native_second_condition(1)",
  "Native_Family_Alignment.native_second_condition(2)",
  "Native_Family_Alignment.native_second_condition(3)",
  "Native_Family_Alignment.native_third_condition(1)",
  "Native_Family_Alignment.native_third_condition(2)",
  "Native_Family_Alignment.native_third_condition(3)",
  "Native_Family_Alignment.same_law_data_all_representations",
  "Native_Family_Alignment.same_transported_input_value",
  "Native_Family_Alignment.same_transported_output_value",
  "Native_Family_Alignment.shared_value_charts"
]\<close>
end
