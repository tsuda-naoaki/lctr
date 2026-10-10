theory Core_Finite_Jets_Vector
  imports "HOL-Analysis.Derivative" "HOL-Computational_Algebra.Polynomial"
begin

definition vderiv :: "(real \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> real \<Rightarrow> 'a" where
  "vderiv f x = vector_derivative f (at x)"

definition curve_smooth :: "(real \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> bool" where
  "curve_smooth f \<longleftrightarrow> (\<forall>n x.
    ((vderiv ^^ n) f has_vector_derivative (vderiv ^^ Suc n) f x) (at x) \<and>
    continuous (at x) ((vderiv ^^ n) f))"

definition power_series_at :: "(real \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> real \<Rightarrow> bool" where
  "power_series_at f a \<longleftrightarrow> (\<exists>b R. 0 < R \<and>
    (\<forall>x. abs (x-a) < R \<longrightarrow> (\<lambda>n. (x-a)^n *\<^sub>R b n) sums f x))"

definition curve_analytic :: "(real \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> bool" where
  "curve_analytic f \<longleftrightarrow> curve_smooth f \<and>
    (\<forall>n a. power_series_at ((vderiv ^^ n) f) a)"

definition basis_poly :: "nat \<Rightarrow> real poly" where
  "basis_poly i = monom (1 / fact i) i"

definition derivative_family ::
  "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> real \<Rightarrow> 'a" where
  "derivative_family n k a v x =
    (\<Sum>i\<le>k. poly ((pderiv ^^ n) (basis_poly i)) (x-a) *\<^sub>R v i)"

definition jet_curve where "jet_curve k a v = derivative_family 0 k a v"
definition monomial where "monomial i a x = poly (basis_poly i) (x-a)"

lemma shifted_poly_derivative:
  "((\<lambda>x::real. poly p (x-a)) has_real_derivative poly (pderiv p) (x-a)) (at x)"
  by (auto intro!: derivative_eq_intros)

lemma derivative_family_has_derivative:
  "(derivative_family n k a v has_vector_derivative derivative_family (Suc n) k a v x) (at x)"
  unfolding derivative_family_def
  apply (rule has_vector_derivative_sum)
  apply (simp only: funpow.simps comp_apply)
  apply (rule has_vector_derivative_scaleR[where g="\<lambda>_. v _" and g'=0, simplified])
   apply (rule shifted_poly_derivative)
  done

lemma vderiv_family:
  "vderiv (derivative_family n k a v) = derivative_family (Suc n) k a v"
  unfolding vderiv_def
  by (rule ext) (rule vector_derivative_at, rule derivative_family_has_derivative)

lemma iterated_curve:
  "(vderiv ^^ n) (jet_curve k a v) = derivative_family n k a v"
  unfolding jet_curve_def
  by (induction n) (simp_all add: vderiv_family)

lemma polynomial_series:
  "(\<lambda>n. coeff (p::real poly) n * x^n) sums poly p x"
  unfolding poly_altdef
  by (rule sums_finite) (auto simp: coeff_eq_0)

lemma finite_polynomial_power_series:
  fixes p :: "nat \<Rightarrow> real poly" and v :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "power_series_at (\<lambda>x. \<Sum>i\<le>k. poly (p i) (x-a) *\<^sub>R v i) b"
proof -
  let ?q = "\<lambda>i. pcompose (p i) [:b-a, 1:]"
  let ?c = "\<lambda>n. \<Sum>i\<le>k. coeff (?q i) n *\<^sub>R v i"
  have s: "(\<lambda>n. (x-b)^n *\<^sub>R ?c n) sums
    (\<Sum>i\<le>k. poly (p i) (x-a) *\<^sub>R v i)" for x
  proof -
    have h: "(\<lambda>n. coeff (?q i) n * (x-b)^n) sums poly (p i) (x-a)" for i
      using polynomial_series[of "?q i" "x-b"]
      by (simp add: poly_pcompose algebra_simps)
    have h': "(\<lambda>n. (coeff (?q i) n * (x-b)^n) *\<^sub>R v i)
      sums (poly (p i) (x-a) *\<^sub>R v i)" for i
      using h[of i] by (rule bounded_linear.sums[OF bounded_linear_scaleR_left])
    show ?thesis using sums_sum[OF h', where I="{..k}"]
      by (simp add: scaleR_sum_right scaleR_scaleR mult.commute)
  qed
  show ?thesis unfolding power_series_at_def
    by (rule exI[of _ ?c], rule exI[of _ 1]) (use s in auto)
qed

lemma curve_smooth_native:
  "curve_smooth (jet_curve k a v)"
  unfolding curve_smooth_def iterated_curve
  using derivative_family_has_derivative
    has_vector_derivative_continuous[OF derivative_family_has_derivative]
  by blast

lemma curve_smooth_all_orders:
  "curve_analytic (jet_curve k a v)"
  unfolding curve_analytic_def
  using curve_smooth_native[of k a v]
  by (auto simp: iterated_curve derivative_family_def[abs_def] intro: finite_polynomial_power_series)

lemma basis_derivative_at_zero:
  "poly ((pderiv ^^ n) (basis_poly i)) 0 = (if n=i then 1 else 0)"
  by (simp add: poly_0_coeff_0 coeff_higher_pderiv basis_poly_def
    pochhammer_fact[symmetric])

lemma curve_derivative:
  assumes "n \<le> k"
  shows "(vderiv ^^ n) (jet_curve k a v) a = v n"
proof -
  have t: "(if n=i then 1 else 0) *\<^sub>R v i = (if i=n then v n else 0)" for i
    by (cases "i=n") auto
  show ?thesis using assms
    by (simp add: iterated_curve derivative_family_def basis_derivative_at_zero t)
qed

lemma monomial_as_curve:
  "monomial i a = jet_curve i a (\<lambda>j. if j=i then 1 else 0)"
proof (rule ext)
  fix x
  have t: "poly (basis_poly j) (x-a) *\<^sub>R (if j=i then (1::real) else 0)
    = (if j=i then poly (basis_poly i) (x-a) else 0)" for j
    by (cases "j=i") auto
  show "monomial i a x = jet_curve i a (\<lambda>j. if j=i then 1 else 0) x"
    by (simp only: monomial_def jet_curve_def derivative_family_def funpow_0 id_apply t) simp
qed

lemma monomial_smooth:
  "curve_analytic (monomial i a)"
  by (simp add: monomial_as_curve curve_smooth_all_orders)

lemma monomial_derivative:
  "(vderiv ^^ n) (monomial i a) a = (if n=i then 1 else 0)"
proof (cases "n\<le>i")
  case True
  show ?thesis using curve_derivative[OF True, of a "\<lambda>j. if j=i then (1::real) else 0"]
    by (simp add: monomial_as_curve)
next
  case False
  have t: "poly ((pderiv ^^ n) (basis_poly j)) 0 = 0" if "j\<le>i" for j
    using False that by (simp add: basis_derivative_at_zero)
  show ?thesis using False
    by (simp add: monomial_as_curve iterated_curve derivative_family_def t)
qed

lemma finite_jet_realization:
  "\<exists>f::real\<Rightarrow>'a::real_normed_vector. curve_analytic f \<and>
    (\<forall>n\<le>k. (vderiv ^^ n) f a = v n)"
  using curve_smooth_all_orders[of k a v] curve_derivative[where k=k and a=a and v=v] by blast

lemma curve_continuous_nhds:
  "continuous (at a) (jet_curve k a v)"
  using curve_smooth_native[of k a v] unfolding curve_smooth_def
  by (metis funpow_0 id_apply)

lemma realization_in_open_value_chart:
  assumes "open V" "v 0 \<in> V"
  shows "\<exists>f::real\<Rightarrow>'a::real_normed_vector. curve_analytic f \<and>
    (\<forall>n\<le>k. (vderiv ^^ n) f a = v n) \<and>
    eventually (\<lambda>x. f x \<in> V) (nhds a)"
proof -
  let ?f = "jet_curve k a v"
  have f0: "?f a = v 0" using curve_derivative[of 0 k a v] by simp
  have c: "filterlim ?f (nhds (?f a)) (nhds a)"
    using curve_continuous_nhds[of a k v] by (simp add: continuous_at tendsto_nhds_iff)
  have nv: "eventually (\<lambda>y. y\<in>V) (nhds (?f a))"
    using assms f0 by (simp add: eventually_nhds_in_open)
  have ev: "eventually (\<lambda>x. ?f x\<in>V) (nhds a)"
    using c nv unfolding filterlim_iff by blast
  show ?thesis by (rule exI[of _ ?f])
    (use curve_smooth_all_orders[of k a v] curve_derivative[where k=k and a=a and v=v] ev in blast)
qed

lemma realization_in_time_and_value_charts:
  assumes "open U" "a\<in>U" "open V" "v 0\<in>V"
  shows "\<exists>f::real\<Rightarrow>'a::real_normed_vector. curve_analytic f \<and>
    (\<forall>n\<le>k. (vderiv ^^ n) f a = v n) \<and>
    eventually (\<lambda>x. x\<in>U \<and> f x\<in>V) (nhds a)"
proof -
  obtain f where f: "curve_analytic f" "\<forall>n\<le>k. (vderiv ^^ n) f a = v n"
    "eventually (\<lambda>x. f x\<in>V) (nhds a)"
    using realization_in_open_value_chart[where V=V and v=v and k=k and a=a, OF assms(3,4)] by blast
  have eu: "eventually (\<lambda>x. x\<in>U) (nhds a)"
    using assms(1,2) by (simp add: eventually_nhds_in_open)
  have e: "eventually (\<lambda>x. x\<in>U \<and> f x\<in>V) (nhds a)"
    using eu f(3) by eventually_elim auto
  show ?thesis using f(1,2) e by blast
qed

definition jet where
  "jet k a f = restrict (\<lambda>n. (vderiv ^^ n) f a) {..k}"

lemma smooth_jet_projection_surjective:
  "(\<lambda>f::real\<Rightarrow>'a::real_normed_vector. jet k a f) ` {f. curve_analytic f}
    = PiE {..k} (\<lambda>_. UNIV)"
proof (rule set_eqI, rule iffI)
  fix v assume "v \<in> (\<lambda>f::real\<Rightarrow>'a. jet k a f) ` {f. curve_analytic f}"
  then show "v \<in> PiE {..k} (\<lambda>_. UNIV)" by (auto simp: jet_def split: if_splits)
next
  fix v::"nat\<Rightarrow>'a" assume v: "v \<in> PiE {..k} (\<lambda>_. UNIV)"
  have e: "jet k a (jet_curve k a v) = v"
    unfolding jet_def using v
    by (auto simp: fun_eq_iff restrict_def PiE_def extensional_def curve_derivative)
  show "v \<in> (\<lambda>f::real\<Rightarrow>'a. jet k a f) ` {f. curve_analytic f}"
    by (rule image_eqI[where x="jet_curve k a v"])
      (simp_all add: e curve_smooth_all_orders)
qed

lemma zeroth_order_control: "jet_curve 0 a v a = v 0"
  using curve_derivative[of 0 0 a v] by simp

ML \<open>
val roots = @{thms monomial_smooth monomial_derivative curve_smooth_all_orders
  curve_derivative finite_jet_realization realization_in_open_value_chart
  realization_in_time_and_value_charts smooth_jet_projection_surjective zeroth_order_control};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
