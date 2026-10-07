theory Native_Metadata_01_043
imports
  "LCTR_Core_Dynamics_Interfaces.Core_Dynamics_Interfaces"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Dynamics_Interfaces.arrival_image_exact",
  "Core_Dynamics_Interfaces.complete_eval_fields",
  "Core_Dynamics_Interfaces.complete_eval_roundtrip",
  "Core_Dynamics_Interfaces.exact_eval_iff",
  "Core_Dynamics_Interfaces.extended_bounded_identity",
  "Core_Dynamics_Interfaces.extended_on_domain",
  "Core_Dynamics_Interfaces.extended_outside_domain",
  "Core_Dynamics_Interfaces.local_relation_typed",
  "Core_Dynamics_Interfaces.quotient_role_membership",
  "Core_Dynamics_Interfaces.reception_pack_roundtrip",
  "Core_Dynamics_Interfaces.reception_unpack_roundtrip",
  "Core_Dynamics_Interfaces.source_relation_typed"
]\<close>
end
