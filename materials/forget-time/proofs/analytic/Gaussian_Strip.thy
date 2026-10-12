theory Gaussian_Strip
  imports "HOL-Probability.Distributions"
begin

definition gaussian :: "real \<Rightarrow> real" where
  "gaussian x = exp (-x\<^sup>2)"

definition thermal_density :: "real \<Rightarrow> real \<Rightarrow> real" where
  "thermal_density q p = exp (-exp (2*q\<^sup>2)*p\<^sup>2) / pi"

lemma gaussian_integral:
  "has_bochner_integral lborel gaussian (sqrt pi)"
  using has_bochner_integral_even_function[OF gaussian_moment_0]
  by (simp add: gaussian_def[abs_def])

lemma gaussian_integrable:
  "integrable lborel gaussian"
  using gaussian_integral by (rule integrable.intros)

lemma gaussian_scaled_integral:
  assumes "0 < c"
  shows "has_bochner_integral lborel (\<lambda>x. exp (-(c*x)\<^sup>2)) (sqrt pi / c)"
  using gaussian_integral assms
    lborel_has_bochner_integral_real_affine_iff[of c gaussian "sqrt pi" 0]
  by (simp add: gaussian_def[abs_def] divide_inverse mult.commute)

lemma thermal_density_positive:
  "0 < thermal_density q p"
  by (simp add: thermal_density_def)

lemma thermal_density_measurable[measurable]:
  "(\<lambda>(q,p). thermal_density q p) \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
  unfolding thermal_density_def by measurable

lemma density_exponent_identity:
  fixes q p :: real
  shows "exp (2*q\<^sup>2)*p\<^sup>2 = (exp (q\<^sup>2)*p)\<^sup>2"
  by (simp only: exp_double power_mult_distrib)

lemma thermal_density_inner_integral:
  "has_bochner_integral lborel (thermal_density q) (exp (-q\<^sup>2) / sqrt pi)"
proof -
  have h: "has_bochner_integral lborel (\<lambda>p. exp (-(exp (q\<^sup>2)*p)\<^sup>2))
      (sqrt pi / exp (q\<^sup>2))"
    by (rule gaussian_scaled_integral) simp
  have "has_bochner_integral lborel (\<lambda>p. exp (-(exp (q\<^sup>2)*p)\<^sup>2) / pi)
      ((sqrt pi / exp (q\<^sup>2)) / pi)"
    using h by (intro has_bochner_integral_divide)
  moreover have "(sqrt pi / exp (q\<^sup>2)) / pi = exp (-q\<^sup>2) / sqrt pi"
    using pi_gt_zero by (simp add: exp_minus field_simps)
  ultimately show ?thesis
    by (simp add: thermal_density_def[abs_def] density_exponent_identity)
qed

lemma thermal_density_normalized_iterated:
  "(\<integral>q. (\<integral>p. thermal_density q p \<partial>lborel) \<partial>lborel) = 1"
proof -
  have inner: "\<And>q. (\<integral>p. thermal_density q p \<partial>lborel) = exp (-q\<^sup>2) / sqrt pi"
    by (rule has_bochner_integral_integral_eq[OF thermal_density_inner_integral])
  have "has_bochner_integral lborel (\<lambda>q. exp (-q\<^sup>2) / sqrt pi) 1"
    using has_bochner_integral_divide[OF gaussian_integral, of "sqrt pi"]
    by (simp add: gaussian_def[abs_def])
  then have integral: "(\<integral>q. exp (-q\<^sup>2) / sqrt pi \<partial>lborel) = 1"
    by (rule has_bochner_integral_integral_eq)
  show ?thesis by (simp only: inner integral)
qed

definition thermal_state :: "(real \<times> real) measure" where
  "thermal_state = density (lborel \<Otimes>\<^sub>M lborel)
    (\<lambda>(q,p). ennreal (thermal_density q p))"

lemma thermal_density_nn_inner:
  "(\<integral>\<^sup>+p. ennreal (thermal_density q p) \<partial>lborel) =
    ennreal (exp (-q\<^sup>2)/sqrt pi)"
proof -
  have int: "integrable lborel (thermal_density q)"
    by (rule integrable.intros[OF thermal_density_inner_integral])
  have pos: "AE p in lborel. 0 \<le> thermal_density q p"
    by (intro AE_I2 less_imp_le thermal_density_positive)
  show ?thesis using nn_integral_eq_integral[OF int pos]
    has_bochner_integral_integral_eq[OF thermal_density_inner_integral] by simp
qed

lemma thermal_density_nn_normalized:
  "(\<integral>\<^sup>+s. ennreal (thermal_density (fst s) (snd s))
      \<partial>(lborel \<Otimes>\<^sub>M lborel)) = 1"
proof -
  have measurable[measurable]: "(\<lambda>s. ennreal (thermal_density (fst s) (snd s)))
      \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    unfolding thermal_density_def by measurable
  have outer: "has_bochner_integral lborel (\<lambda>q. exp (-q\<^sup>2)/sqrt pi) 1"
    using has_bochner_integral_divide[OF gaussian_integral, of "sqrt pi"]
    by (simp add: gaussian_def[abs_def])
  have ni: "(\<integral>\<^sup>+q. ennreal (exp (-q\<^sup>2)/sqrt pi) \<partial>lborel) = 1"
  proof -
    have pos: "AE q in lborel. 0 \<le> exp (-q\<^sup>2)/sqrt pi" by simp
    have eq: "(\<integral>\<^sup>+q. ennreal (exp (-q\<^sup>2)/sqrt pi) \<partial>lborel) =
        ennreal (\<integral>q. exp (-q\<^sup>2)/sqrt pi \<partial>lborel)"
      by (rule nn_integral_eq_integral[OF integrable.intros[OF outer] pos])
    show ?thesis using eq
      by (simp only: has_bochner_integral_integral_eq[OF outer] ennreal_1)
  qed
  have "(\<integral>\<^sup>+q. \<integral>\<^sup>+p. ennreal (thermal_density q p) \<partial>lborel \<partial>lborel) = 1"
    by (simp only: thermal_density_nn_inner ni)
  moreover have "(\<integral>\<^sup>+q. \<integral>\<^sup>+p. ennreal (thermal_density q p) \<partial>lborel \<partial>lborel) =
      (\<integral>\<^sup>+s. ennreal (thermal_density (fst s) (snd s)) \<partial>(lborel \<Otimes>\<^sub>M lborel))"
    using lborel.nn_integral_fst[OF measurable] by simp
  ultimately show ?thesis by simp
qed

theorem thermal_state_probability:
  "prob_space thermal_state"
proof
  have measurable[measurable]: "(\<lambda>(q,p). ennreal (thermal_density q p))
      \<in> borel_measurable (lborel \<Otimes>\<^sub>M lborel)"
    unfolding thermal_density_def by measurable
  show "emeasure thermal_state (space thermal_state) = 1"
    unfolding thermal_state_def
    apply (simp only: space_density)
    apply (subst emeasure_density[OF measurable])
     apply (rule sets.top)
    apply (simp only: space_pair_measure space_lborel space_borel UNIV_Times_UNIV indicator_UNIV mult_1_right case_prod_beta thermal_density_nn_normalized)
    done
qed

end
