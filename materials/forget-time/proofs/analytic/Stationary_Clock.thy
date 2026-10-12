theory Stationary_Clock
  imports "HOL-Probability.Probability"
begin

context prob_space
begin

theorem stationary_affine_reading:
  fixes T :: "'a \<Rightarrow> real" and phi :: "'a \<Rightarrow> 'a" and k :: real
  assumes Tm[measurable]: "T \<in> borel_measurable M"
    and pm[measurable]: "phi \<in> measurable M M"
    and invariant: "distr M M phi = M"
    and affine: "AE x in M. T (phi x) = T x + k"
  shows "k = 0"
proof -
  let ?f = "\<lambda>x. arctan (T x)"
  let ?g = "\<lambda>x. arctan (T (phi x))"
  have bounded: "\<And>z. norm (arctan z) \<le> pi/2"
  proof -
    fix z :: real
    show "norm (arctan z) \<le> pi/2"
      using arctan_bounded[of z] by (simp add: real_norm_def abs_le_iff; linarith)
  qed
  have fi: "integrable M ?f"
    by (rule integrable_const_bound[where B="pi/2"])
      (intro AE_I2 bounded, measurable)
  have gi: "integrable M ?g"
    by (rule integrable_const_bound[where B="pi/2"])
      (intro AE_I2 bounded, measurable)
  have same: "(\<integral>x. ?f x \<partial>M) = (\<integral>x. ?g x \<partial>M)"
    using Bochner_Integration.integral_distr[OF pm, of ?f] invariant by simp
  have mass: "emeasure M (space M) \<noteq> 0"
    using emeasure_space_1 by simp
  have notpos: "\<not> 0 < k"
  proof
    assume k: "0 < k"
    have lt: "AE x in M. ?f x < ?g x"
      using affine by eventually_elim (simp add: arctan_less_iff k)
    have "(\<integral>x. ?f x \<partial>M) < (\<integral>x. ?g x \<partial>M)"
      by (rule integral_less_AE_space[OF fi gi lt mass])
    then show False using same by simp
  qed
  have notneg: "\<not> k < 0"
  proof
    assume k: "k < 0"
    have lt: "AE x in M. ?g x < ?f x"
      using affine by eventually_elim (simp add: arctan_less_iff k)
    have "(\<integral>x. ?g x \<partial>M) < (\<integral>x. ?f x \<partial>M)"
      by (rule integral_less_AE_space[OF gi fi lt mass])
    then show False using same by simp
  qed
  show ?thesis using notpos notneg by linarith
qed

end

end
