theory Native_Metadata_01_038
imports
  "LCTR_Core_Differential_Tokens.Core_Differential_Tokens"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Differential_Tokens.atlas_failure_blocks_descendants",
  "Core_Differential_Tokens.incoming_edges_exact",
  "Core_Differential_Tokens.law_failure_blocks_differential",
  "Core_Differential_Tokens.matching_differential.failure_set_token_image",
  "Core_Differential_Tokens.matching_differential.finite_witness_set",
  "Core_Differential_Tokens.matching_differential.minimal_token_correspondence",
  "Core_Differential_Tokens.matching_differential.relative_nonemptiness",
  "Core_Differential_Tokens.matching_differential.relative_nonempty_witness_family",
  "Core_Differential_Tokens.matching_differential.signature_token_correspondence",
  "Core_Differential_Tokens.ready_failure",
  "Core_Differential_Tokens.recursive_failure",
  "Core_Differential_Tokens.token_bijection",
  "Core_Differential_Tokens.within_edges_exact"
]\<close>
end
