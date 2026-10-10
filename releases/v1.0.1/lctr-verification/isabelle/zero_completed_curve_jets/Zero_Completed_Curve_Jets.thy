theory Zero_Completed_Curve_Jets
  imports "LCTR_Zero_Completed_Derivative.Zero_Completed_Derivative"
    "LCTR_Core_Curve_Regularity.Core_Curve_Regularity"
begin

lemma higher_curve_zderiv_Suc:
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes S: "open S"
  shows "higher_differentiable_on S f (Suc n) \<longleftrightarrow>
    (\<forall>x\<in>S. f differentiable (at x)) \<and> higher_differentiable_on S (zderiv f) n"
proof (cases "\<forall>x\<in>S. f differentiable (at x)")
  case True
  have eq: "zderiv f x = frechet_derivative f (at x) 1" if "x\<in>S" for x
    using frechet_derivative_eq_vector_derivative[OF True[rule_format, OF that]]
    by (simp add: zderiv_def True[rule_format, OF that])
  have h: "higher_differentiable_on S (zderiv f) n \<longleftrightarrow>
      higher_differentiable_on S (\<lambda>x. frechet_derivative f (at x) 1) n"
    by (rule higher_differentiable_on_cong[OF S refl eq])
  show ?thesis by (simp only: higher_differentiable_on_real_Suc[OF S] h)
next
  case False
  show ?thesis by (simp add: higher_differentiable_on_real_Suc[OF S] False)
qed

lemma higher_curve_iterated_zderiv:
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes S: "open S" and h: "higher_differentiable_on S f (n+m)"
  shows "higher_differentiable_on S ((zderiv ^^ n) f) m"
  using h
proof (induction n arbitrary: f)
  case 0 then show ?case by simp
next
  case (Suc n)
  have d: "higher_differentiable_on S (zderiv f) (n+m)"
    using Suc.prems by (simp add: higher_curve_zderiv_Suc[OF S])
  have ih: "higher_differentiable_on S ((zderiv ^^ n) (zderiv f)) m"
    by (rule Suc.IH[OF d])
  show ?case using ih by (simp only: funpow_Suc_right comp_apply)
qed

lemma higher_curve_iterated_derivatives_agree:
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector"
  assumes S: "open S" and h: "higher_differentiable_on S f k" and n: "n\<le>k" and x: "x\<in>S"
  shows "(zderiv ^^ n) f x = (vderiv ^^ n) f x"
  using n x
proof (induction n arbitrary: x)
  case 0 show ?case by simp
next
  case (Suc n)
  have nk: "n\<le>k" and step: "n+Suc (k-Suc n)=k" using Suc.prems(1) by auto
  have hd: "higher_differentiable_on S ((zderiv ^^ n) f) (Suc (k-Suc n))"
    by (rule higher_curve_iterated_zderiv[OF S]) (simp only: step; rule h)
  have diff: "(zderiv ^^ n) f differentiable (at x)"
    using hd Suc.prems(2)
    by (auto simp only: higher_differentiable_on.simps)
  have ev: "eventually (\<lambda>y. y\<in>S) (nhds x)"
    using S Suc.prems(2) by (simp add: eventually_nhds_in_open)
  have agree: "eventually (\<lambda>y. (zderiv ^^ n) f y = (vderiv ^^ n) f y) (nhds x)"
    using ev by eventually_elim (rule Suc.IH[OF nk], assumption)
  have v: "vderiv ((zderiv ^^ n) f) x = vderiv ((vderiv ^^ n) f) x"
    by (rule vderiv_germ[OF agree])
  show ?case by (simp only: funpow.simps comp_apply zderiv_on_domain[OF diff] v)
qed

definition zjet where
  "zjet k a f = restrict (\<lambda>n. (zderiv ^^ n) f a) {..k}"

lemma curve_ck_zjet_agrees:
  assumes "curve_ck_at k a f"
  shows "zjet k a f = jet k a f"
proof -
  obtain S where S: "open S" "a\<in>S" "higher_differentiable_on S f k"
    using assms unfolding curve_ck_at_def by blast
  show ?thesis unfolding zjet_def jet_def
    by (rule ext) (auto simp: restrict_def intro: higher_curve_iterated_derivatives_agree[OF S(1,3) _ S(2)])
qed

lemma zjet_in_domain:
  "f a\<in>V \<Longrightarrow> zjet k a f\<in>jet_domain k V"
  by (auto simp: zjet_def jet_domain_def restrict_def PiE_def extensional_def)

lemma zjet_domain_realization:
  assumes v: "v\<in>jet_domain k V"
  obtains f where "curve_ck_at k a f" "f a\<in>V" "zjet k a f=v"
proof -
  obtain f where f: "curve_ck_at k a f" "f a\<in>V" "jet k a f=v"
    using jet_domain_realization[OF v] by blast
  show ?thesis by (rule that[OF f(1,2)]) (simp add: curve_ck_zjet_agrees[OF f(1)] f(3))
qed

ML \<open>
val roots = @{thms higher_curve_zderiv_Suc higher_curve_iterated_zderiv
  higher_curve_iterated_derivatives_agree curve_ck_zjet_agrees zjet_in_domain zjet_domain_realization};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
