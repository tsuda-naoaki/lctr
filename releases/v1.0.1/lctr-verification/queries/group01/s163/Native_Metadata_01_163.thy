theory Native_Metadata_01_163
imports
  "LCTR_Law_Datum_Final_Alignment.Law_Datum_Final_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Law_Datum_Final_Alignment.candidate_condition_vector",
  "Law_Datum_Final_Alignment.dynamics_law_failures_disjoint",
  "Law_Datum_Final_Alignment.failure_matches_native_family",
  "Law_Datum_Final_Alignment.failure_on_selected_datum",
  "Law_Datum_Final_Alignment.failure_vs_operative",
  "Law_Datum_Final_Alignment.fixed_carrier_operative_exact",
  "Law_Datum_Final_Alignment.law_failure_requires_dynamics",
  "Law_Datum_Final_Alignment.law_operative_on_selected_datum",
  "Law_Datum_Final_Alignment.outside_selection_not_failure",
  "Law_Datum_Final_Alignment.selected_all_conditions_exact",
  "Law_Datum_Final_Alignment.selected_condition_exact",
  "Law_Datum_Final_Alignment.selected_datum_ready"
]\<close>
end
