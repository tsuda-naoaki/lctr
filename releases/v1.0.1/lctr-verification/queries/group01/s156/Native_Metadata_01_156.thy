theory Native_Metadata_01_156
imports
  "LCTR_Core_Validity_Maximum.Core_Validity_Maximum"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Validity_Maximum.empty_family_no_maximum",
  "Core_Validity_Maximum.full_domain_membership",
  "Core_Validity_Maximum.greatest_equals_union",
  "Core_Validity_Maximum.incomparable_family_no_maximum",
  "Core_Validity_Maximum.maximum_exists_iff_union_member",
  "Core_Validity_Maximum.maximum_unique",
  "Core_Validity_Maximum.maximum_validity_domain",
  "Core_Validity_Maximum.union_is_greatest"
]\<close>
end
