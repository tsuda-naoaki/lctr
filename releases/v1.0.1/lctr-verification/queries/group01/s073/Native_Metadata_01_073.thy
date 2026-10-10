theory Native_Metadata_01_073
imports
  "LCTR_Core_Joint_Time_Seed.Core_Joint_Time_Seed"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Joint_Time_Seed.common_seed_time.time_maps_inverse",
  "Core_Joint_Time_Seed.common_seed_time.time_order_agrees",
  "Core_Joint_Time_Seed.common_seed_time.time_order_forward",
  "Core_Joint_Time_Seed.common_seed_time.time_projection_agrees",
  "Core_Joint_Time_Seed.common_seed_time.time_quotient_types_equal",
  "Core_Joint_Time_Seed.common_seed_time.time_setoids_equal"
]\<close>
end
