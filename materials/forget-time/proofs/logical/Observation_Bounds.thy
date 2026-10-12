theory Observation_Bounds
  imports Complex_Main
begin

theorem record_fibre_obstruction:
  assumes "record x = record y" "value x \<noteq> value y"
  shows "\<not> (\<exists>reconstruct. \<forall>z. reconstruct (record z) = value z)"
  using assms by metis

theorem two_point_error_lower_bound:
  fixes a b r :: real
  shows "abs (a-b) / 2 \<le> max (abs (r-a)) (abs (r-b))"
proof -
  have "abs (a-b) \<le> abs (r-a) + abs (r-b)"
    using abs_triangle_ineq[of "a-r" "r-b"] by (simp add: abs_minus_commute)
  moreover have "abs (r-a) \<le> max (abs (r-a)) (abs (r-b))" by simp
  moreover have "abs (r-b) \<le> max (abs (r-a)) (abs (r-b))" by simp
  ultimately show ?thesis by linarith
qed

corollary record_fibre_error:
  fixes valof :: "'a \<Rightarrow> real"
  assumes "record x = record y"
  shows "abs (valof x - valof y) / 2 \<le>
    max (abs (estimate (record x) - valof x))
        (abs (estimate (record y) - valof y))"
  using two_point_error_lower_bound[of "valof x" "valof y" "estimate (record x)"]
    assms by simp

definition admissible_scale :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "admissible_scale N m sigma lam \<longleftrightarrow>
    0 < lam \<and> sigma*lam \<le> 1 \<and> m*lam/N \<le> 1 \<and> lam/N \<le> 1"

theorem admissible_scale_interval:
  assumes "0 < N" "0 < m" "0 < sigma"
  shows "admissible_scale N m sigma lam \<longleftrightarrow>
    0 < lam \<and> lam \<le> min (1/sigma) (min (N/m) N)"
  using assms by (auto simp: admissible_scale_def le_divide_eq divide_le_eq mult.commute)

lemma coupling_upgrade_monotone:
  assumes "s2 \<le> s1" "admissible_scale N m s1 lam"
  shows "admissible_scale N m s2 lam"
proof -
  have pos: "0 \<le> lam" using assms(2) by (simp add: admissible_scale_def)
  have bound: "s2*lam \<le> s1*lam" by (rule mult_right_mono[OF assms(1) pos])
  show ?thesis using assms(2) bound by (auto simp: admissible_scale_def; linarith)
qed

lemma device_scale_example:
  "admissible_scale 100 2 (1/100) 30"
  "\<not> admissible_scale 100 2 (1/25) 30"
  by (simp add: admissible_scale_def)+

theorem correlation_error_composition:
  fixes omega :: "'a::real_normed_algebra \<Rightarrow> complex"
    and E T B :: 'a and classical :: complex
    and C eps_ev eps_stat :: real
  assumes diff: "\<And>x y. omega x - omega y = omega (x-y)"
    and contract: "\<And>x. norm (omega x) \<le> norm x"
    and evolution: "norm (E-T) \<le> eps_ev"
    and observable: "norm B \<le> C"
    and state: "norm (omega (T*B) - classical) \<le> eps_stat"
  shows "norm (omega (E*B) - classical) \<le> C*eps_ev + eps_stat"
proof -
  have nonneg: "0 \<le> eps_ev" "0 \<le> C"
    using evolution observable norm_ge_zero[of "E-T"] norm_ge_zero[of B] by linarith+
  have "norm (omega (E*B) - omega (T*B)) \<le> norm ((E-T)*B)"
    by (simp only: diff left_diff_distrib) (rule contract)
  also have "... \<le> norm (E-T) * norm B" by (rule norm_mult_ineq)
  also have "... \<le> eps_ev * C"
    using evolution observable nonneg by (intro mult_mono) auto
  finally have ev: "norm (omega (E*B) - omega (T*B)) \<le> C*eps_ev"
    by (simp add: mult.commute)
  have "norm (omega (E*B) - classical) \<le>
    norm (omega (E*B) - omega (T*B)) + norm (omega (T*B) - classical)"
    using norm_triangle_ineq[of "omega (E*B) - omega (T*B)" "omega (T*B) - classical"]
    by simp
  then show ?thesis using ev state by linarith
qed

end
