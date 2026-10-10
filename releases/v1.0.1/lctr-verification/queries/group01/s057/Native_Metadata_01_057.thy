theory Native_Metadata_01_057
imports
  "LCTR_Core_Finite_Jets_Vector.Core_Finite_Jets_Vector"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Finite_Jets_Vector.curve_derivative",
  "Core_Finite_Jets_Vector.curve_smooth_all_orders",
  "Core_Finite_Jets_Vector.finite_jet_realization",
  "Core_Finite_Jets_Vector.monomial_derivative",
  "Core_Finite_Jets_Vector.monomial_smooth",
  "Core_Finite_Jets_Vector.realization_in_open_value_chart",
  "Core_Finite_Jets_Vector.realization_in_time_and_value_charts",
  "Core_Finite_Jets_Vector.smooth_jet_projection_surjective",
  "Core_Finite_Jets_Vector.zeroth_order_control"
]\<close>
end
