theory Core_Continuum_Integration_Alignment
  imports LCTR_Core_Continuum_Integration.Core_Continuum_Integration
begin
lemmas all_sat_iff_tests = Core_Continuum_Integration.all_sat_iff_tests
lemmas approx_predecessor_kinds = Core_Continuum_Integration.approx_predecessor_kinds

lemma approx_index_image:
  "(\<lambda>i::nat. (3,Suc i)) ` {..<9} = approx_set"
proof
  show "(\<lambda>i::nat. (3,Suc i)) ` {..<9} \<subseteq> approx_set"
    unfolding approx_set_exact by auto
  show "approx_set \<subseteq> (\<lambda>i::nat. (3,Suc i)) ` {..<9}"
  proof
    fix t :: token
    assume "t\<in>approx_set"
    then obtain i where t: "t=(3,i)" and low: "1\<le>i" and high: "i\<le>9"
      unfolding approx_set_exact by blast
    have idx: "i-1<9" and recovered_idx: "Suc (i-1)=i" using low high by arith+
    have mem: "i-1\<in>{..<9}" using idx by simp
    have eq: "t=(3::nat,Suc (i-1))" using t recovered_idx by simp
    have "(3::nat,Suc (i-1))\<in>(\<lambda>j::nat. (3,Suc j)) ` {..<9}"
      by (rule imageI[OF mem])
    then show "t\<in>(\<lambda>i::nat. (3,Suc i)) ` {..<9}" using eq by blast
  qed
qed

lemma approx_index_bijection:
  "bij_betw (\<lambda>i::nat. (3,Suc i)) {..<9} approx_set"
  unfolding bij_betw_def
  using approx_index_image by (auto simp: inj_on_def)

lemma approx_all_iff:
  "(\<forall>t\<in>approx_set. P t) = (\<forall>i<9. P (3,Suc i))"
  by (subst approx_index_image[symmetric]) (auto simp: lessThan_iff)

lemmas approx_states_iff_conditions = Core_Continuum_Integration.approx_states_iff_conditions
lemmas quantitative_validity = Core_Continuum_Integration.quantitative_validity
lemmas operational_first_excess = Core_Continuum_Integration.operational_first_excess

ML \<open>
val roots = @{thms all_sat_iff_tests approx_predecessor_kinds approx_index_bijection
  approx_all_iff approx_states_iff_conditions quantitative_validity operational_first_excess};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
