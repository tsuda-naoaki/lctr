theory Native_Metadata_01_139
imports
  "LCTR_Core_Representation_Stages.Core_Representation_Stages"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Representation_Stages.control_domains_cover",
  "Core_Representation_Stages.control_domains_overlap",
  "Core_Representation_Stages.control_local_strict_empty",
  "Core_Representation_Stages.local_cover_does_not_force_global_inc",
  "Core_Representation_Stages.representation_base.condition_hierarchy",
  "Core_Representation_Stages.representation_base.exact_condition_expansion",
  "Core_Representation_Stages.representation_base.exact_preserves_comparison_gate",
  "Core_Representation_Stages.representation_base.first_creates_actual_order",
  "Core_Representation_Stages.representation_base.first_payload_retained",
  "Core_Representation_Stages.representation_base.original_payload_retained",
  "Core_Representation_Stages.representation_base.second_creates_actual_charts",
  "Core_Representation_Stages.representation_base.second_payload_retained",
  "Core_Representation_Stages.representation_base.third_creates_actual_embeddings"
]\<close>
end
