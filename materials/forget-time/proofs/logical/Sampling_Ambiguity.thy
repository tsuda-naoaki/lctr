theory Sampling_Ambiguity
  imports Observation_Bounds
begin

definition base_sample_model :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "base_sample_model q p t = q + 2*p*t"

definition perturbed_sample_model :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "perturbed_sample_model q p N t = q + 2*p*t + sin (2*pi*N*t)/(8*pi*N)"

lemma sample_models_agree:
  assumes "N \<noteq> 0"
  shows "perturbed_sample_model q p N (real k/N) = base_sample_model q p (real k/N)"
proof -
  have angle: "2*pi*N*(real k/N) = real (2*k)*pi"
    using assms by (simp add: field_simps)
  show ?thesis
    by (simp only: perturbed_sample_model_def base_sample_model_def angle sin_npi; simp)
qed

lemma base_sample_derivative:
  "DERIV (base_sample_model q p) t :> 2*p"
  unfolding base_sample_model_def by (auto intro!: derivative_eq_intros)

lemma perturbed_sample_derivative:
  assumes "N \<noteq> 0"
  shows "DERIV (perturbed_sample_model q p N) t :> (2*p + cos (2*pi*N*t)/4)"
  unfolding perturbed_sample_model_def
  using assms by (auto intro!: derivative_eq_intros simp: field_simps)

lemma derivative_at_samples:
  assumes "N \<noteq> 0"
  shows "DERIV (perturbed_sample_model q p N) (real k/N) :> (2*p + 1/4)"
proof -
  have angle: "2*pi*N*(real k/N) = real (2*k)*pi"
    using assms by (simp add: field_simps)
  show ?thesis using perturbed_sample_derivative[OF assms, of q p "real k/N"]
    by (simp only: angle cos_npi power_mult; simp)
qed

lemma sample_value_error_bound:
  assumes "0 < N"
  shows "abs (perturbed_sample_model q p N t - base_sample_model q p t) \<le> 1/(8*pi*N)"
proof -
  have pos: "0 < 8*pi*N" using assms by (intro mult_pos_pos) simp_all
  show ?thesis using abs_sin_le_one[of "2*pi*N*t"] pos
    by (simp add: perturbed_sample_model_def base_sample_model_def abs_divide divide_le_cancel)
qed

lemma perturbed_derivative_positive:
  assumes "3/16 \<le> p"
  shows "1/8 \<le> 2*p + cos (2*pi*N*t)/4"
  using assms cos_ge_minus_one[of "2*pi*N*t"] by linarith

theorem perturbed_strictly_increasing:
  assumes "N \<noteq> 0" "3/16 \<le> p"
  shows "strict_mono (perturbed_sample_model q p N)"
proof (rule strict_monoI)
  fix x y :: real assume xy: "x < y"
  show "perturbed_sample_model q p N x < perturbed_sample_model q p N y"
  proof (rule DERIV_pos_imp_increasing[OF xy])
    fix t :: real
    have d: "DERIV (perturbed_sample_model q p N) t :> (2*p + cos (2*pi*N*t)/4)"
      by (rule perturbed_sample_derivative[OF assms(1)])
    have "0 < 2*p + cos (2*pi*N*t)/4"
      using perturbed_derivative_positive[OF assms(2), of N t] by linarith
    with d show "\<exists>d. DERIV (perturbed_sample_model q p N) t :> d \<and> 0 < d"
      by blast
  qed
qed

theorem sampled_derivative_error:
  fixes estimate :: "real list \<Rightarrow> real"
    and q p N :: real and ks :: "nat list"
  assumes "N \<noteq> 0"
  defines "xs \<equiv> map (\<lambda>k. base_sample_model q p (real k/N)) ks"
    and "ys \<equiv> map (\<lambda>k. perturbed_sample_model q p N (real k/N)) ks"
  shows "xs = ys"
    and "1/8 \<le> max (abs (estimate xs - 2*p))
      (abs (estimate ys - (2*p+1/4)))"
proof -
  show eq: "xs = ys"
    unfolding xs_def ys_def using sample_models_agree[OF assms(1)] by simp
  have "abs (2*p-(2*p+1/4))/2 \<le>
      max (abs (estimate xs - 2*p)) (abs (estimate xs - (2*p+1/4)))"
    by (rule two_point_error_lower_bound)
  then show "1/8 \<le> max (abs (estimate xs - 2*p))
      (abs (estimate ys - (2*p+1/4)))"
    using eq by simp
qed

end
