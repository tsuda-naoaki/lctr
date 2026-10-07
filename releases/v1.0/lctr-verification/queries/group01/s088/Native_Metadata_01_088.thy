theory Native_Metadata_01_088
imports
  "LCTR_Core_Local_Jet_Membership_Bridge.Core_Local_Jet_Membership_Bridge"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Local_Jet_Membership_Bridge.generated_image_member"
]\<close>
end
