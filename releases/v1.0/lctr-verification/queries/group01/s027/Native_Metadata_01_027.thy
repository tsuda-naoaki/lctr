theory Native_Metadata_01_027
imports
  "LCTR_Core_Continuum_Native_Cells.Core_Continuum_Native_Cells"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Continuum_Native_Cells.mapped_full_image",
  "Core_Continuum_Native_Cells.native_record_cells.both_families_width_bound",
  "Core_Continuum_Native_Cells.native_record_cells.both_families_width_excess",
  "Core_Continuum_Native_Cells.native_record_cells.comparison_cell_exact",
  "Core_Continuum_Native_Cells.native_record_cells.comparison_native_witness",
  "Core_Continuum_Native_Cells.native_record_cells.full_cell_images_preserved",
  "Core_Continuum_Native_Cells.native_record_cells.native_width_source_supremum",
  "Core_Continuum_Native_Cells.native_record_cells.observer_cell_exact",
  "Core_Continuum_Native_Cells.native_record_cells.observer_native_witness"
]\<close>
end
