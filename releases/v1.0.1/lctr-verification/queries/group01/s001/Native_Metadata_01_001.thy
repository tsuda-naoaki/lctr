theory Native_Metadata_01_001
imports
  "LCTR_Chapter02_Role_Alignment.Chapter02_Role_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Chapter02_Role_Alignment.alignment_body_abstraction_source_preserved",
  "Chapter02_Role_Alignment.alignment_different_indices_remain_distinct_at_each_role",
  "Chapter02_Role_Alignment.alignment_different_role_positions_remain_distinct",
  "Chapter02_Role_Alignment.alignment_distinct_zeta_same_object_scene_and_bind_witness",
  "Chapter02_Role_Alignment.alignment_distinct_zeta_same_specified_data_still_distinct_in_every_role",
  "Chapter02_Role_Alignment.alignment_realizationRole_cases",
  "Chapter02_Role_Alignment.alignment_realization_input_excludes_body",
  "Chapter02_Role_Alignment.alignment_realization_is_additional_and_preserves_existing_ri",
  "Chapter02_Role_Alignment.alignment_riFamily_preserves_index_and_role_positions",
  "Chapter02_Role_Alignment.alignment_roleInstance_eq_iff_index_eq",
  "Chapter02_Role_Alignment.alignment_section2_synthesis_body_source",
  "Chapter02_Role_Alignment.alignment_section2_synthesis_preserves_positions",
  "Chapter02_Role_Alignment.alignment_section2_synthesis_realization_domain"
]\<close>
end
