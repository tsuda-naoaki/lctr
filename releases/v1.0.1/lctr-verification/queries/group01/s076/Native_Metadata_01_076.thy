theory Native_Metadata_01_076
imports
  "LCTR_Core_Law_Countercases.Core_Law_Countercases"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Law_Countercases.alternate_output_is_distinct",
  "Core_Law_Countercases.condition135_remainders",
  "Core_Law_Countercases.condition1_countercases",
  "Core_Law_Countercases.condition2_countercase",
  "Core_Law_Countercases.condition2_remainder",
  "Core_Law_Countercases.condition3_countercases",
  "Core_Law_Countercases.condition4_countercases",
  "Core_Law_Countercases.condition4_remainder",
  "Core_Law_Countercases.condition5_cases_exclusive",
  "Core_Law_Countercases.condition5_countercases",
  "Core_Law_Countercases.generated_conflict_is_global",
  "Core_Law_Countercases.pair_remainder"
]\<close>
end
