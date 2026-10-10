theory Native_Metadata_01_155
imports
  "LCTR_Core_Universal_Factorization.Core_Universal_Factorization"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Universal_Factorization.comparison_factor_unique",
  "Core_Universal_Factorization.comparison_relation_factorization",
  "Core_Universal_Factorization.order_quotient_factor.quotient_factor_commutes",
  "Core_Universal_Factorization.order_quotient_factor.quotient_factor_exists_unique",
  "Core_Universal_Factorization.order_quotient_factor.quotient_factor_strict_order",
  "Core_Universal_Factorization.overlap_factor_naturality",
  "Core_Universal_Factorization.precomposition_cancellation",
  "Core_Universal_Factorization.reparametrization_unique",
  "Core_Universal_Factorization.surjective_factor_exists_unique"
]\<close>
end
