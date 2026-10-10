theory Native_Metadata_01_137
imports
  "LCTR_Core_Representation_Failure_Stages.Core_Representation_Failure_Stages"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Representation_Failure_Stages.representation_base.condition_values",
  "Core_Representation_Failure_Stages.representation_base.generated_stage_one",
  "Core_Representation_Failure_Stages.representation_base.generated_stage_three",
  "Core_Representation_Failure_Stages.representation_base.generated_stage_two",
  "Core_Representation_Failure_Stages.representation_base.global_condition_exact",
  "Core_Representation_Failure_Stages.representation_base.global_condition_on_formed_input",
  "Core_Representation_Failure_Stages.representation_base.local_condition_exact",
  "Core_Representation_Failure_Stages.representation_base.local_condition_on_formed_input",
  "Core_Representation_Failure_Stages.representation_base.native_failure_domain",
  "Core_Representation_Failure_Stages.representation_base.native_failure_signature",
  "Core_Representation_Failure_Stages.representation_base.native_first_failure_four_points",
  "Core_Representation_Failure_Stages.representation_base.native_second_failure_triple",
  "Core_Representation_Failure_Stages.representation_base.native_second_failure_witness",
  "Core_Representation_Failure_Stages.representation_base.native_stage_failure_one",
  "Core_Representation_Failure_Stages.representation_base.native_stage_failure_three",
  "Core_Representation_Failure_Stages.representation_base.native_stage_failure_two",
  "Core_Representation_Failure_Stages.representation_base.native_third_failure_triple",
  "Core_Representation_Failure_Stages.representation_base.native_third_failure_witness"
]\<close>
end
