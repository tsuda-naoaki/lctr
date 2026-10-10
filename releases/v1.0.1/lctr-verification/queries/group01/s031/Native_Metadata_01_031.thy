theory Native_Metadata_01_031
imports
  "LCTR_Core_Countable_Chart_Boundary.Core_Countable_Chart_Boundary"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Countable_Chart_Boundary.all_sources_uncountable",
  "Core_Countable_Chart_Boundary.countable_tagged_sources_iff",
  "Core_Countable_Chart_Boundary.each_source_countable",
  "Core_Countable_Chart_Boundary.empty_time_domain_allows_empty_cover",
  "Core_Countable_Chart_Boundary.no_nonempty_countable_cover",
  "Core_Countable_Chart_Boundary.open_chart_domain_empty",
  "Core_Countable_Chart_Boundary.real_open_countable_empty"
]\<close>
end
