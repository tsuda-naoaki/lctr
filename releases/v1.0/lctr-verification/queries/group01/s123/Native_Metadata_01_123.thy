theory Native_Metadata_01_123
imports
  "LCTR_Core_Raw_Comparison_Entry.Core_Raw_Comparison_Entry"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Raw_Comparison_Entry.configuration_comparison_seed.entered_residual",
  "Core_Raw_Comparison_Entry.configuration_comparison_seed.failed_entry_blocks",
  "Core_Raw_Comparison_Entry.configuration_comparison_seed.full_conditions_generate",
  "Core_Raw_Comparison_Entry.configuration_comparison_seed.full_master_condition",
  "Core_Raw_Comparison_Entry.configuration_comparison_seed.guardedG_before_entry",
  "Core_Raw_Comparison_Entry.configuration_comparison_seed.operative_iff_residual",
  "Core_Raw_Comparison_Entry.guarded_step_iff"
]\<close>
end
