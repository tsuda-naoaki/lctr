theory Zero_Completed_Jet_Germs
  imports "LCTR_Zero_Completed_Curve_Jets.Zero_Completed_Curve_Jets"
begin

lemma vector_differentiability_germ:
  fixes f g :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes eq: "eventually (\<lambda>x. f x = g x) (nhds a)"
  shows "f differentiable (at a) \<longleftrightarrow> g differentiable (at a)"
proof -
  have point: "f a = g a" by (rule eventually_nhds_x_imp_x[OF eq])
  have deriv: "(f has_vector_derivative v) (at a) \<longleftrightarrow>
      (g has_vector_derivative v) (at a)" for v
    using has_vector_derivative_cong_ev[where S=UNIV and x=a and f=f and g=g and f'=v]
      eq point by simp
  show ?thesis
    using deriv vector_derivative_works differentiableI_vector by meson
qed

lemma zderiv_germ:
  assumes eq: "eventually (\<lambda>x. f x = g x) (nhds a)"
  shows "zderiv f a = zderiv g a"
  by (simp add: zderiv_def vector_differentiability_germ[OF eq]
      vderiv_germ[OF eq, unfolded vderiv_def])

lemma iterated_zderiv_germ:
  assumes "eventually (\<lambda>x. f x = g x) (nhds a)"
  shows "eventually (\<lambda>x. (zderiv ^^ n) f x = (zderiv ^^ n) g x) (nhds a)"
  using assms
proof (induction n)
  case 0 then show ?case by simp
next
  case (Suc n)
  have ev: "eventually (\<lambda>x. eventually (\<lambda>y.
      (zderiv ^^ n) f y = (zderiv ^^ n) g y) (nhds x)) (nhds a)"
    using Suc.IH[OF Suc.prems] by (simp only: eventually_eventually)
  show ?case using ev by eventually_elim (simp add: zderiv_germ)
qed

lemma zjet_germ:
  assumes "eventually (\<lambda>x. f x = g x) (nhds a)"
  shows "zjet k a f = zjet k a g"
  unfolding zjet_def
  using eventually_nhds_x_imp_x[OF iterated_zderiv_germ[OF assms]]
  by (auto simp: restrict_def fun_eq_iff)

lemma zjet_zeroth: "zjet k a f 0 = f a"
  by (simp add: zjet_def restrict_def)

lemma zjet_polynomial_global_realization:
  assumes v: "v\<in>jet_domain k V"
  obtains f where "\<And>m. higher_differentiable_on UNIV f m"
    "f a\<in>V" "zjet k a f=v"
proof -
  let ?f = "jet_curve k a v"
  have regular: "higher_differentiable_on UNIV ?f m" for m
    unfolding jet_curve_def by (rule derivative_family_ck)
  have v0: "v 0\<in>V" and vp: "v\<in>PiE {..k} (\<lambda>_. UNIV)"
    using v by (auto simp: jet_domain_def)
  have value_at_a: "?f a = v 0"
    using zderiv_polynomial_jet[where n=0 and k=k and a=a and v=v] by simp
  have jet_eq: "zjet k a ?f = v"
    using vp by (auto simp: zjet_def restrict_def fun_eq_iff PiE_def extensional_def
        zderiv_polynomial_jet)
  show ?thesis by (rule that[OF regular]) (simp_all add: value_at_a v0 jet_eq)
qed

lemma empty_value_chart_control: "jet_domain k {} = {}"
  by (simp add: jet_domain_def)

ML \<open>
val roots = @{thms vector_differentiability_germ zderiv_germ iterated_zderiv_germ
  zjet_germ zjet_zeroth zjet_polynomial_global_realization empty_value_chart_control};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
