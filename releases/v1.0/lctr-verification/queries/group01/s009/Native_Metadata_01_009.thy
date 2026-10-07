theory Native_Metadata_01_009
imports
  "LCTR_Core_Chart_Overlaps.Core_Chart_Overlaps"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Chart_Overlaps.ambient_restriction_image",
  "Core_Chart_Overlaps.base_eq_coordinate_equiv",
  "Core_Chart_Overlaps.coordinate_overlaps.chart_commutes",
  "Core_Chart_Overlaps.coordinate_overlaps.chart_forward_formula",
  "Core_Chart_Overlaps.coordinate_overlaps.coordinate_domain_formula",
  "Core_Chart_Overlaps.coordinate_overlaps.coordinate_injective",
  "Core_Chart_Overlaps.realExtension_inverse",
  "Core_Chart_Overlaps.realExtension_maps",
  "Core_Chart_Overlaps.realExtension_on_domain",
  "Core_Chart_Overlaps.restricted_relation_image",
  "Core_Chart_Overlaps.time_image_coordinate_overlaps.chart_link_for_time_images"
]\<close>
end
