theory Native_Metadata_01_078
imports
  "LCTR_Core_Law_Datum_Transport.Core_Law_Datum_Transport"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Law_Datum_Transport.generated_common_representability",
  "Core_Law_Datum_Transport.law_transport.admissible_image",
  "Core_Law_Datum_Transport.law_transport.common_image",
  "Core_Law_Datum_Transport.law_transport.condition_preserved",
  "Core_Law_Datum_Transport.law_transport.evaluation_tuple_transport",
  "Core_Law_Datum_Transport.law_transport.law_operative_preserved",
  "Core_Law_Datum_Transport.law_transport.specification_preserved"
]\<close>
end
