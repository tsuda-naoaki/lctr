theory Native_Metadata_01_127
imports
  "LCTR_Core_Record_Cells.Core_Record_Cells"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Record_Cells.affine_frequency.singleton_width_zero",
  "Core_Record_Cells.affine_frequency.span_agrees_with_every_witness",
  "Core_Record_Cells.affine_frequency.width_nonnegative",
  "Core_Record_Cells.affine_frequency.width_witness_independent",
  "Core_Record_Cells.empty_has_no_extrema",
  "Core_Record_Cells.extrema_ordered",
  "Core_Record_Cells.extrema_unique",
  "Core_Record_Cells.has_ext_iff",
  "Core_Record_Cells.record_affine.admissible_nonempty_cell_has_bounded_width",
  "Core_Record_Cells.record_affine.width_admissibility_contract",
  "Core_Record_Cells.record_representation.associated_image_nonempty",
  "Core_Record_Cells.record_representation.cell_image_membership",
  "Core_Record_Cells.record_representation.cell_image_nonempty",
  "Core_Record_Cells.record_representation.collision_excludes_separation",
  "Core_Record_Cells.record_representation.missing_record_excludes_separation",
  "Core_Record_Cells.record_representation.record_value_factorization",
  "Core_Record_Cells.record_representation.record_value_kernel",
  "Core_Record_Cells.record_representation.representation_injective",
  "Core_Record_Cells.record_representation.separation_exact_contract"
]\<close>
end
