theory Native_Metadata_02_006
imports
  "LCTR_Core_Typed_Words_Alignment.Core_Typed_Words_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Typed_Words_Alignment.action_functional",
  "Core_Typed_Words_Alignment.action_injective",
  "Core_Typed_Words_Alignment.append_action",
  "Core_Typed_Words_Alignment.append_domain",
  "Core_Typed_Words_Alignment.disjoint_union_tag_bridge",
  "Core_Typed_Words_Alignment.empty_action",
  "Core_Typed_Words_Alignment.overlapping_regions_lose_tags",
  "Core_Typed_Words_Alignment.reverse_action",
  "Core_Typed_Words_Alignment.tagged_words.loop_identity_iff_local_projection_injective",
  "Core_Typed_Words_Alignment.tagged_words.orbit_equivalence",
  "Core_Typed_Words_Alignment.typed_actions.reverse_domain"
]\<close>
end
