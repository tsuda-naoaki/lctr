theory Native_Metadata_01_095
imports
  "LCTR_Core_Native_Differential_Predicates.Core_Native_Differential_Predicates"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Native_Differential_Predicates.canonical_pair_from_any_realization",
  "Core_Native_Differential_Predicates.diff2_exact",
  "Core_Native_Differential_Predicates.diff2_iff_smooth_realizations",
  "Core_Native_Differential_Predicates.diff3_false_outside",
  "Core_Native_Differential_Predicates.diff3_realization_independent",
  "Core_Native_Differential_Predicates.diff3_requires_diff2",
  "Core_Native_Differential_Predicates.diff3_restricts",
  "Core_Native_Differential_Predicates.real_transported_atlas.canonical_pair_transport",
  "Core_Native_Differential_Predicates.real_transported_atlas.diff2_transport",
  "Core_Native_Differential_Predicates.real_transported_atlas.diff3_transport",
  "Core_Native_Differential_Predicates.real_transported_atlas.transported_total_curve",
  "Core_Native_Differential_Predicates.total_curve_on_domain"
]\<close>
end
