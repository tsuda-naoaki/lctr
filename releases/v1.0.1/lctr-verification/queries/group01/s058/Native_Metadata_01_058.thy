theory Native_Metadata_01_058
imports
  "LCTR_Core_Finite_Mixed_Reduction.Core_Finite_Mixed_Reduction"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Finite_Mixed_Reduction.native_comparison.deletion_preserves_transport_count",
  "Core_Finite_Mixed_Reduction.native_comparison.mixed_indexed_trace",
  "Core_Finite_Mixed_Reduction.native_comparison.mixed_reduction_trace",
  "Core_Finite_Mixed_Reduction.native_comparison.reduction_preserves_transport_count",
  "Core_Finite_Mixed_Reduction.native_comparison.reduction_trace",
  "Core_Finite_Mixed_Reduction.native_comparison.terminal_classification",
  "Core_Finite_Mixed_Reduction.native_comparison.terminal_transport_display",
  "Core_Finite_Mixed_Reduction.native_comparison.trace_domain_extension",
  "Core_Finite_Mixed_Reduction.native_comparison.trace_exact_on_old_domain"
]\<close>
end
