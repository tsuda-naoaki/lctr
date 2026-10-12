theory Measurement_Integral_Bounds
  imports "HOL-Probability.Probability" "Thermal_Logical_Core.Observation_Bounds"
begin

context finite_measure
begin

theorem supported_measurement_error:
  fixes f g b :: "'a \<Rightarrow> complex" and C eps :: real
  assumes int: "integrable M (\<lambda>x. f x * b x)" "integrable M (\<lambda>x. g x * b x)"
    and V: "V \<in> sets M"
    and bounds: "\<And>x. x \<in> space M \<Longrightarrow> norm (b x) \<le> C"
    and support: "\<And>x. x \<in> space M \<Longrightarrow> x \<notin> V \<Longrightarrow> b x = 0"
    and error: "\<And>x. x \<in> V \<Longrightarrow> norm (f x - g x) \<le> eps"
    and nonneg: "0 \<le> C" "0 \<le> eps"
  shows "norm ((\<integral>x. f x * b x \<partial>M) - (\<integral>x. g x * b x \<partial>M))
      \<le> C * measure M V * eps"
proof -
  let ?d = "\<lambda>x. f x * b x - g x * b x"
  have dint: "integrable M ?d" by (rule Bochner_Integration.integrable_diff[OF int])
  have Vf: "emeasure M V < \<infinity>"
    using emeasure_finite[of V] by (simp only: infinity_ennreal_def less_top)
  have indint: "integrable M (indicator V :: 'a \<Rightarrow> real)"
    by (rule Bochner_Integration.integrable_real_indicator[OF V Vf])
  have point: "\<And>x. x \<in> space M \<Longrightarrow> norm (?d x) \<le> C*eps*indicator V x"
  proof -
    fix x assume x: "x \<in> space M"
    show "norm (?d x) \<le> C*eps*indicator V x"
    proof (cases "x \<in> V")
      case True
      have "norm (?d x) = norm (f x-g x)*norm (b x)"
        by (simp add: left_diff_distrib[symmetric] norm_mult)
      also have "... \<le> eps*C"
        by (intro mult_mono error[OF True] bounds[OF x] nonneg) auto
      finally show ?thesis using True by (simp add: mult.commute)
    next
      case False
      then show ?thesis using support[OF x] by simp
    qed
  qed
  have "norm (\<integral>x. ?d x \<partial>M) \<le> (\<integral>x. norm (?d x) \<partial>M)"
    by (rule Bochner_Integration.integral_norm_bound)
  also have "... \<le> (\<integral>x. C*eps*indicator V x \<partial>M)"
    by (intro Bochner_Integration.integral_mono Bochner_Integration.integrable_norm dint
      Bochner_Integration.integrable_mult_right indint)
      (use point in auto)
  also have "... = C*eps*measure M V" using V by simp
  finally show ?thesis using int
    by (simp add: Bochner_Integration.integral_diff mult.commute mult.left_commute)
qed

theorem quantum_measurement_error:
  fixes omega :: "'b::real_normed_algebra \<Rightarrow> complex"
    and E T B :: 'b and f g b :: "'a \<Rightarrow> complex"
    and C D eps_ev eps_stat eps_clk :: real
  assumes diff: "\<And>x y. omega x - omega y = omega (x-y)"
    and contract: "\<And>x. norm (omega x) \<le> norm x"
    and evolution: "norm (E-T) \<le> eps_ev"
    and observable: "norm B \<le> C"
    and state: "norm (omega (T*B) - (\<integral>x. f x*b x \<partial>M)) \<le> eps_stat"
    and int: "integrable M (\<lambda>x. f x*b x)" "integrable M (\<lambda>x. g x*b x)"
    and V: "V \<in> sets M"
    and bounds: "\<And>x. x \<in> space M \<Longrightarrow> norm (b x) \<le> D"
    and support: "\<And>x. x \<in> space M \<Longrightarrow> x \<notin> V \<Longrightarrow> b x = 0"
    and error: "\<And>x. x \<in> V \<Longrightarrow> norm (f x-g x) \<le> eps_clk"
    and nonneg: "0 \<le> D" "0 \<le> eps_clk"
  shows "norm (omega (E*B) - (\<integral>x. g x*b x \<partial>M))
    \<le> C*eps_ev + eps_stat + D*measure M V*eps_clk"
proof -
  have q: "norm (omega (E*B) - (\<integral>x. f x*b x \<partial>M)) \<le> C*eps_ev+eps_stat"
    by (rule correlation_error_composition[OF diff contract evolution observable state])
  have m: "norm ((\<integral>x. f x*b x \<partial>M) - (\<integral>x. g x*b x \<partial>M))
      \<le> D*measure M V*eps_clk"
    by (rule supported_measurement_error[OF int V bounds support error nonneg])
  have "norm (omega (E*B) - (\<integral>x. g x*b x \<partial>M)) \<le>
      norm (omega (E*B) - (\<integral>x. f x*b x \<partial>M)) +
      norm ((\<integral>x. f x*b x \<partial>M) - (\<integral>x. g x*b x \<partial>M))"
    using norm_triangle_ineq[of "omega (E*B) - (\<integral>x. f x*b x \<partial>M)"
      "(\<integral>x. f x*b x \<partial>M) - (\<integral>x. g x*b x \<partial>M)"] by simp
  then show ?thesis using q m by linarith
qed

end

end
