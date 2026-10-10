theory Value_Jet_Analytic_Realization
  imports "LCTR_Zero_Completed_Jet_Germs.Zero_Completed_Jet_Germs"
begin

lemma analytic_zjet_agrees:
  assumes "curve_analytic f"
  shows "zjet k a f=jet k a f"
proof -
  have sm: "curve_smooth f" using assms unfolding curve_analytic_def by blast
  show ?thesis by (simp add: zjet_def jet_def zderiv_smooth_iterate[OF sm])
qed

lemma analytic_zero_completed_derivative_series:
  assumes "curve_analytic f"
  shows "power_series_at ((zderiv ^^ n) f) a"
proof -
  have sm: "curve_smooth f" using assms unfolding curve_analytic_def by blast
  have ps: "power_series_at ((vderiv ^^ n) f) a" using assms unfolding curve_analytic_def by blast
  show ?thesis by (simp only: zderiv_smooth_iterate[OF sm] ps)
qed

lemma domain_realization:
  assumes v: "v\<in>jet_domain k V"
  obtains f where "curve_analytic f" "f a\<in>V" "zjet k a f=v"
proof -
  let ?f = "jet_curve k a v"
  have analytic: "curve_analytic ?f" by (rule curve_smooth_all_orders)
  have v0: "v 0\<in>V" and vp: "v\<in>PiE {..k} (\<lambda>_. UNIV)"
    using v by (auto simp: jet_domain_def)
  have c0: "?f a=v 0" using curve_derivative[where n=0 and k=k and a=a and v=v] by simp
  have jet_eq: "jet k a ?f=v"
    using vp by (auto simp: jet_def restrict_def fun_eq_iff PiE_def extensional_def curve_derivative)
  show ?thesis by (rule that[OF analytic])
    (simp_all add: c0 v0 analytic_zjet_agrees[OF analytic] jet_eq)
qed

ML \<open>
val roots = @{thms analytic_zjet_agrees analytic_zero_completed_derivative_series domain_realization};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
