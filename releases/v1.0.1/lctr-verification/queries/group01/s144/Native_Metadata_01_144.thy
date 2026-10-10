theory Native_Metadata_01_144
imports
  "LCTR_Core_Source_Loops.Core_Source_Loops"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Source_Loops.native_comparison.append_length",
  "Core_Source_Loops.native_comparison.delete_source_loop_action",
  "Core_Source_Loops.native_comparison.deletion_exact_on_old_domain",
  "Core_Source_Loops.native_comparison.deletion_extends_action",
  "Core_Source_Loops.native_comparison.deletion_extends_domain",
  "Core_Source_Loops.native_comparison.deletion_strictly_shortens",
  "Core_Source_Loops.native_comparison.finite_source_reduction",
  "Core_Source_Loops.native_comparison.gluing_iff_local_injectivity",
  "Core_Source_Loops.native_comparison.pure_and_irreducible_mixed_give_all_loops",
  "Core_Source_Loops.native_comparison.pure_iff_all_loops_under_mixed",
  "Core_Source_Loops.native_comparison.reduction_exact_on_old_domain",
  "Core_Source_Loops.native_comparison.reduction_extends_action",
  "Core_Source_Loops.native_comparison.source_loop_identity",
  "Core_Source_Loops.native_comparison.source_path_preserves_recovery"
]\<close>
end
