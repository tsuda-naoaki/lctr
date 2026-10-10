theory Core_Continuum_Encoding_Alignment
  imports LCTR_Core_Continuum_Encoding.Core_Continuum_Encoding
begin
lemmas half_exact = Core_Continuum_Encoding.half_exact
lemmas midpoint_encoding = Core_Continuum_Encoding.midpoint_encoding
lemmas midpoint_margin = Core_Continuum_Encoding.midpoint_margin
lemmas midpoint_positive_margin = Core_Continuum_Encoding.midpoint_positive_margin
lemmas nine_component_encoding = Core_Continuum_Encoding.nine_component_encoding
lemmas first_six_preserved = Core_Continuum_Encoding.first_six_preserved
lemmas final_three_margin = Core_Continuum_Encoding.final_three_margin
lemmas source_quantitative_validity = source_approximation_encoding.source_quantitative_validity
lemmas source_robust_validity = source_approximation_encoding.source_robust_validity

lemma wrong_threshold_controls:
  "\<not>0<margin 0 (bool_defect True) \<and> bool_defect False\<le>(1::ereal)"
  using Core_Continuum_Encoding.wrong_threshold_controls by blast

ML \<open>
val roots = @{thms half_exact midpoint_encoding midpoint_margin midpoint_positive_margin
  nine_component_encoding first_six_preserved final_three_margin source_quantitative_validity
  source_robust_validity wrong_threshold_controls};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
