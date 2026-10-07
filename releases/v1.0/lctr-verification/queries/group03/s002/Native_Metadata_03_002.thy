theory Native_Metadata_03_002
imports
  "LCTR_Core_Word_Domain_Definitions.Core_Word_Domain_Definitions"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Word_Domain_Definitions.empty_identity",
  "Core_Word_Domain_Definitions.fix_subset_domain",
  "Core_Word_Domain_Definitions.identity_iff_fixed_domain",
  "Core_Word_Domain_Definitions.restricted_typed_actions.restricted_action",
  "Core_Word_Domain_Definitions.restricted_typed_actions.restricted_inverse",
  "Core_Word_Domain_Definitions.typed_actions.erased_orbit_exact_if_disjoint",
  "Core_Word_Domain_Definitions.typed_actions.erased_orbit_word_witness",
  "Core_Word_Domain_Definitions.typed_actions.loop_identity_exact"
]\<close>
end
