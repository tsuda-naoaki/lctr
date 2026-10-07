theory Native_Metadata_01_161
imports
  "LCTR_Generic_Native_Overlap_Alignment.Generic_Native_Overlap_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Generic_Native_Overlap_Alignment.bound_time_relation_image",
  "Generic_Native_Overlap_Alignment.bound_value_relation_image",
  "Generic_Native_Overlap_Alignment.chart_change_bijective",
  "Generic_Native_Overlap_Alignment.chart_change_formula",
  "Generic_Native_Overlap_Alignment.chart_change_inverse",
  "Generic_Native_Overlap_Alignment.overlap_image_formula",
  "Generic_Native_Overlap_Alignment.overlap_image_in_target",
  "Generic_Native_Overlap_Alignment.overlap_value_injective",
  "Generic_Native_Overlap_Alignment.product_chart_at_generated_values",
  "Generic_Native_Overlap_Alignment.product_chart_region",
  "Generic_Native_Overlap_Alignment.time_change_from_actual_charts",
  "Generic_Native_Overlap_Alignment.value_change_from_actual_charts"
]\<close>
end
