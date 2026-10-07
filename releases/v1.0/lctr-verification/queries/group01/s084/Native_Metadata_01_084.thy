theory Native_Metadata_01_084
imports
  "LCTR_Core_Law_State.Core_Law_State"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Law_State.native_law_state.direct_pass_iff_ancestors",
  "Core_Law_State.native_law_state.ideal_failed_iff",
  "Core_Law_State.native_law_state.ideal_recursion",
  "Core_Law_State.native_law_state.ideal_sat_iff",
  "Core_Law_State.native_law_state.recursive_completion_iff",
  "Core_Law_State.native_law_state.recursive_failed_iff",
  "Core_Law_State.native_law_state.recursive_failure_exists_iff",
  "Core_Law_State.native_law_state.recursive_state_unique",
  "Core_Law_State.native_law_state.total_ancestor_condition"
]\<close>
end
