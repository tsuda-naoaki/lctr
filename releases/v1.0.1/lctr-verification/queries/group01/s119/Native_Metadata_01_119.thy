theory Native_Metadata_01_119
imports
  "LCTR_Core_Pure_Word_Displays.Core_Pure_Word_Displays"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Pure_Word_Displays.direction_length",
  "Core_Pure_Word_Displays.native_comparison.source_display_injective",
  "Core_Pure_Word_Displays.native_comparison.source_positions_suffice",
  "Core_Pure_Word_Displays.native_comparison.source_unique_display_preimage",
  "Core_Pure_Word_Displays.native_comparison.transport_display_injective",
  "Core_Pure_Word_Displays.native_comparison.transport_unique_display_preimage",
  "Core_Pure_Word_Displays.native_position_length",
  "Core_Pure_Word_Displays.pure_display_shapes",
  "Core_Pure_Word_Displays.source_direction_is_not_transport",
  "Core_Pure_Word_Displays.source_kind_list_constant",
  "Core_Pure_Word_Displays.transport_kinds_recovered"
]\<close>
end
