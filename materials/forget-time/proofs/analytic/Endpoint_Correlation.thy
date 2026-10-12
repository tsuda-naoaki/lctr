theory Endpoint_Correlation
  imports Strip_Flow "Thermal_Logical_Core.Endpoint_Completions"
begin

context finite_measure
begin

theorem weighted_strict_gap:
  fixes a b w :: "'a \<Rightarrow> real" and c :: real
  assumes int: "integrable M (\<lambda>x. a x*w x)" "integrable M (\<lambda>x. b x*w x)" "integrable M w"
    and nonneg: "AE x in M. 0\<le>w x"
    and gap: "AE x in M. 0<w x \<longrightarrow> c<a x-b x"
    and wm: "w \<in> borel_measurable M"
    and positive: "0 < emeasure M {x\<in>space M. 0<w x}"
  shows "c*(\<integral>x. w x \<partial>M) <
    (\<integral>x. a x*w x \<partial>M) - (\<integral>x. b x*w x \<partial>M)"
proof -
  let ?f = "\<lambda>x. c*w x"
  let ?g = "\<lambda>x. a x*w x-b x*w x"
  have fi: "integrable M ?f" by (rule Bochner_Integration.integrable_mult_right[OF int(3)])
  have gi: "integrable M ?g" by (rule Bochner_Integration.integrable_diff[OF int(1,2)])
  have strict: "AE x in M. 0<w x \<longrightarrow> ?f x<?g x"
    using gap by eventually_elim
      (auto simp: left_diff_distrib[symmetric] intro: mult_strict_right_mono)
  have le: "AE x in M. ?f x\<le>?g x"
    using strict nonneg by eventually_elim (auto; linarith)
  have setm: "{x\<in>space M. 0<w x}\<in>sets M" using wm by measurable
  have nz: "emeasure M {x\<in>space M. 0<w x}\<noteq>0" using positive by simp
  have ne: "AE x in M. x\<in>{x\<in>space M. 0<w x} \<longrightarrow> ?f x\<noteq>?g x"
    using strict by eventually_elim auto
  have "(\<integral>x. ?f x \<partial>M)<(\<integral>x. ?g x \<partial>M)"
    by (rule integral_less_AE[OF fi gi nz setm ne le])
  then show ?thesis using int by (simp add: Bochner_Integration.integral_diff)
qed

theorem endpoint_correlation_gap:
  fixes Y w :: "'a \<Rightarrow> real" and L :: real
  assumes L: "0<L"
    and int: "integrable M (\<lambda>x. reflecting_position L (Y x)*w x)"
      "integrable M (\<lambda>x. periodic_position L (Y x)*w x)" "integrable M w"
    and nonneg: "AE x in M. 0\<le>w x"
    and support: "AE x in M. 0<w x \<longrightarrow> (5*L/4<Y x \<and> Y x<7*L/4)"
    and wm: "w\<in>borel_measurable M"
    and positive: "0<emeasure M {x\<in>space M. 0<w x}"
  shows "L/2*(\<integral>x. w x \<partial>M) <
    (\<integral>x. reflecting_position L (Y x)*w x \<partial>M) -
    (\<integral>x. periodic_position L (Y x)*w x \<partial>M)"
proof (rule weighted_strict_gap[OF int nonneg _ wm positive])
  show "AE x in M. 0<w x \<longrightarrow>
    L/2<reflecting_position L (Y x)-periodic_position L (Y x)"
    using support by eventually_elim (meson endpoint_difference[OF L])
qed

end

end
