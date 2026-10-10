theory Native_Metadata_01_085
imports
  "LCTR_Core_Law_Transport_Identity.Core_Law_Transport_Identity"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Law_Transport_Identity.component_identity_transport",
  "Core_Law_Transport_Identity.conjugate_identity_transport",
  "Core_Law_Transport_Identity.family_identity_transport",
  "Core_Law_Transport_Identity.identity_law_transport.faithful_identity_transport",
  "Core_Law_Transport_Identity.identity_law_transport.family_identity_from_values",
  "Core_Law_Transport_Identity.identity_reindex_unique",
  "Core_Law_Transport_Identity.tuple_identity_reindex"
]\<close>
end
