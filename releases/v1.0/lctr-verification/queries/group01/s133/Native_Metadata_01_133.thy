theory Native_Metadata_01_133
imports
  "LCTR_Core_Relative_State_Profile.Core_Relative_State_Profile"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Relative_State_Profile.combined_outputs_independent",
  "Core_Relative_State_Profile.fibers_disjoint",
  "Core_Relative_State_Profile.four_state_cover",
  "Core_Relative_State_Profile.full_iff_sat_universe",
  "Core_Relative_State_Profile.profile_and_localization_agree",
  "Core_Relative_State_Profile.unique_series_membership",
  "Core_Relative_State_Profile.unique_state_membership"
]\<close>
end
