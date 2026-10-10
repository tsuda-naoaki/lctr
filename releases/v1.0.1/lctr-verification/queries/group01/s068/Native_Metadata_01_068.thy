theory Native_Metadata_01_068
imports
  "LCTR_Core_Joint_Descent_Alignment.Core_Joint_Descent_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Joint_Descent_Alignment.carrier_saturation.domain_criterion",
  "Core_Joint_Descent_Alignment.carrier_saturation.relation_criterion",
  "Core_Joint_Descent_Alignment.empty_domain_control",
  "Core_Joint_Descent_Alignment.missing_domain_saturation_control",
  "Core_Joint_Descent_Alignment.missing_surjectivity_control",
  "Core_Joint_Descent_Alignment.native_joint_descent",
  "Core_Joint_Descent_Alignment.prodPrj_kernel",
  "Core_Joint_Descent_Alignment.prodPrj_surjective",
  "Core_Joint_Descent_Alignment.quotient_pair_unique",
  "Core_Joint_Descent_Alignment.quotient_relation_typed"
]\<close>
end
