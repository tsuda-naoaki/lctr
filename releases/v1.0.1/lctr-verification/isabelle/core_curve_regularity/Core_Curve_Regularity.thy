theory Core_Curve_Regularity
  imports "LCTR_AFP_Smooth_Library.Smooth"
    "LCTR_Core_Finite_Jets_Vector.Core_Finite_Jets_Vector"
begin

definition curve_ck_at :: "nat \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> bool" where
  "curve_ck_at k a f \<longleftrightarrow> (\<exists>S. open S \<and> a\<in>S \<and> higher_differentiable_on S f k)"

lemma vderiv_germ:
  assumes "eventually (\<lambda>x. f x = g x) (nhds a)"
  shows "vderiv f a = vderiv g a"
  unfolding vderiv_def
  using vector_derivative_cong_eq[where A=UNIV and B=UNIV and x=a and y=a and f=f and g=g] assms
  by simp

lemma iterated_vderiv_germ:
  assumes "eventually (\<lambda>x. f x = g x) (nhds a)"
  shows "eventually (\<lambda>x. (vderiv ^^ n) f x = (vderiv ^^ n) g x) (nhds a)"
  using assms
proof (induction n)
  case 0 then show ?case by simp
next
  case (Suc n)
  have e: "eventually (\<lambda>x. eventually (\<lambda>y. (vderiv ^^ n) f y = (vderiv ^^ n) g y) (nhds x)) (nhds a)"
    using Suc.IH[OF Suc.prems] by (simp only: eventually_eventually)
  show ?case using e
    by eventually_elim (simp add: vderiv_germ)
qed

lemma jet_germ:
  assumes "eventually (\<lambda>x. f x = g x) (nhds a)"
  shows "jet k a f = jet k a g"
  unfolding jet_def
  using eventually_nhds_x_imp_x[OF iterated_vderiv_germ[OF assms]]
  by (auto simp: restrict_def fun_eq_iff)

lemma derivative_family_ck:
  "higher_differentiable_on UNIV (derivative_family n k a v) m"
proof (induction m arbitrary: n)
  case 0
  have "continuous (at x) (derivative_family n k a v)" for x
    by (rule has_vector_derivative_continuous[OF derivative_family_has_derivative])
  then show ?case
    unfolding higher_differentiable_on.simps(1) continuous_on_eq_continuous_at[OF open_UNIV]
    by auto
next
  case (Suc m)
  have d: "derivative_family n k a v differentiable at x" for x
    using derivative_family_has_derivative[of n k a v x]
    by (auto simp: has_vector_derivative_def differentiable_def)
  have eq: "(\<lambda>x. frechet_derivative (derivative_family n k a v) (at x) 1) = derivative_family (Suc n) k a v"
    using frechet_derivative_eq_vector_derivative[OF d]
      vderiv_family[of n k a v]
    by (auto simp: fun_eq_iff vderiv_def)
  show ?case
    by (simp only: higher_differentiable_on_real_Suc[OF open_UNIV] eq)
       (use d Suc.IH[of "Suc n"] in auto)
qed

lemma jet_curve_ck:
  "curve_ck_at k a (jet_curve n b v)"
  unfolding curve_ck_at_def jet_curve_def
  using derivative_family_ck[where n=0 and k=n and a=b and v=v and m=k]
  by (rule_tac x=UNIV in exI) auto

lemma curve_ck_on_at:
  "open S \<Longrightarrow> a\<in>S \<Longrightarrow> higher_differentiable_on S f k \<Longrightarrow> curve_ck_at k a f"
  unfolding curve_ck_at_def by blast

lemma curve_ck_comp:
  fixes f :: "real \<Rightarrow> 'a::real_normed_vector" and g :: "real \<Rightarrow> real"
  assumes f: "curve_ck_at k (g a) f" and g: "curve_ck_at k a g"
  shows "curve_ck_at k a (f \<circ> g)"
proof -
  obtain T where T: "open T" "g a\<in>T" "higher_differentiable_on T f k"
    using f unfolding curve_ck_at_def by blast
  obtain S where S: "open S" "a\<in>S" "higher_differentiable_on S g k"
    using g unfolding curve_ck_at_def by blast
  have c: "continuous_on S g"
    by (rule higher_differentiable_on_imp_continuous_on[OF S(3)])
  have o: "open (S \<inter> g -` T)"
    using c T(1) continuous_on_open_vimage[OF S(1), of g]
    by (simp add: Int_commute)
  have d: "higher_differentiable_on (S \<inter> g -` T) g k"
    by (rule higher_differentiable_on_subset[OF S(3)]) auto
  have h: "higher_differentiable_on (S \<inter> g -` T) (f \<circ> g) k"
    by (rule higher_differentiable_on_compose[OF T(3) d _ o T(1)]) auto
  show ?thesis using o S(2) T(2) h unfolding curve_ck_at_def by blast
qed

definition jet_domain :: "nat \<Rightarrow> 'a set \<Rightarrow> (nat \<Rightarrow> 'a) set" where
  "jet_domain k V = {v\<in>PiE {..k} (\<lambda>_. UNIV). v 0\<in>V}"

lemma jet_in_domain:
  "f a\<in>V \<Longrightarrow> jet k a f\<in>jet_domain k V"
  by (auto simp: jet_domain_def jet_def restrict_def PiE_def extensional_def)

lemma jet_domain_realization:
  assumes v: "v\<in>jet_domain k V"
  obtains c where "curve_ck_at k a c" "c a\<in>V" "jet k a c=v"
proof -
  let ?c = "jet_curve k a v"
  have v0: "v 0\<in>V" and vp: "v\<in>PiE {..k} (\<lambda>_. UNIV)"
    using v by (auto simp: jet_domain_def)
  have e: "jet k a ?c=v"
    using vp by (auto simp: jet_def restrict_def fun_eq_iff PiE_def extensional_def curve_derivative)
  have c0: "?c a=v 0" using curve_derivative[of 0 k a v] by simp
  show ?thesis by (rule that[OF jet_curve_ck _ e]) (simp add: c0 v0)
qed

ML \<open>
val roots = @{thms jet_germ derivative_family_ck jet_curve_ck curve_ck_comp jet_domain_realization};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
