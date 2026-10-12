theory Concrete_Correlation
  imports Periodic_Group Endpoint_Correlation
begin

definition crossing_rectangle :: "real \<Rightarrow> real \<Rightarrow> (real\<times>real) set" where
  "crossing_rectangle L u={L/2<..<3*L/4}\<times>{3*L/(8*u)<..<L/(2*u)}"

definition bounded_position :: "real \<Rightarrow> real\<times>real \<Rightarrow> real" where
  "bounded_position L x=max (-L) (min L (fst x))"

lemma bounded_position_bound:
  assumes "0<L"
  shows "abs(bounded_position L x)\<le>L"
  using assms unfolding bounded_position_def by (simp add: abs_le_iff)

lemma bounded_position_exact:
  assumes "-L\<le>q" "q\<le>L"
  shows "bounded_position L (q,p)=q"
  using assms by (simp add: bounded_position_def)

lemma crossing_rectangle_measurable[measurable]:
  "crossing_rectangle L u\<in>sets(strip_state L)"
  unfolding crossing_rectangle_def strip_state_def gaussian_state_def by measurable

lemma crossing_rectangle_bounds:
  assumes L: "0<L" and u: "0<u" and x: "x\<in>crossing_rectangle L u"
  shows "0<snd x" "5*L/4<fst x+2 * snd x*u" "fst x+2 * snd x*u<7*L/4"
proof -
  have q: "L/2<fst x" "fst x<3*L/4"
    and p: "3*L/(8*u)<snd x" "snd x<L/(2*u)"
    using x by (auto simp: crossing_rectangle_def)
  have lo: "3*L<snd x*(8*u)" using p(1) u by (simp add: divide_less_eq)
  have hi: "snd x*(2*u)<L" using p(2) u by (simp add: less_divide_eq)
  have "0<3*L/(8*u)" using L u by (simp add: divide_pos_pos)
  then show "0<snd x" using p(1) by linarith
  show "5*L/4<fst x+2 * snd x*u" using q lo by (simp add: algebra_simps; linarith)
  show "fst x+2 * snd x*u<7*L/4" using q hi by (simp add: algebra_simps; linarith)
qed

theorem crossing_rectangle_positive:
  assumes L: "0<L" and u: "0<u"
  shows "0<emeasure (strip_state L) (crossing_rectangle L u)"
proof -
  interpret G: prob_space gaussian_state by (rule gaussian_state_probability)
  have ab: "3*L/(8*u)<L/(2*u)" using L u by (simp add: field_simps; linarith)
  have gp: "0<emeasure gaussian_state {3*L/(8*u)<..<L/(2*u)}"
    by (rule gaussian_interval_positive[OF ab])
  have inter: "{-L<..<L}\<inter>{L/2<..<3*L/4}={L/2<..<3*L/4}"
    using L by (auto; linarith)
  have up: "0<emeasure (uniform_measure lborel {-L<..<L}) {L/2<..<3*L/4}"
    using L by (simp add: inter ennreal_zero_less_divide)
  show ?thesis unfolding strip_state_def crossing_rectangle_def
    by (subst G.emeasure_pair_measure_Times)
      (use up gp in \<open>auto simp: gaussian_state_def ennreal_zero_less_mult_iff\<close>)
qed

lemma bounded_position_measurable[measurable]:
  "bounded_position L\<in>borel_measurable(strip_state L)"
  unfolding bounded_position_def strip_state_def gaussian_state_def by measurable

lemma periodic_motion_measurable[measurable]:
  "periodic_motion L u\<in>measurable(strip_state L)(strip_state L)"
  unfolding periodic_motion_def periodic_position_def wrap_def frac_def strip_state_def gaussian_state_def by measurable

lemma reflection_motion_strip_measurable[measurable]:
  "reflection_motion L u\<in>measurable(strip_state L)(strip_state L)"
  using reflection_maps_measurable(3)[of L u]
  by (simp only: measurable_cong_sets[OF strip_state_sets strip_state_sets])

lemma crossing_observable_gap:
  assumes L: "0<L" and u: "0<u" and x: "x\<in>crossing_rectangle L u"
  shows "L/2<bounded_position L (reflection_motion L u x)-bounded_position L (periodic_motion L u x)"
proof -
  let ?Y = "fst x+2 * snd x*u"
  have p: "0<snd x" and y: "5*L/4<?Y" "?Y<7*L/4"
    using crossing_rectangle_bounds[OF L u x] by blast+
  have yr: "L<?Y" "?Y<3*L" using L y by linarith+
  have ref: "reflection_motion L u x=(2*L-?Y,-snd x)"
    using reflection_first_crossing[OF L p yr] by (simp add: prod.collapse)
  have per: "periodic_motion L u x=(?Y-2*L,snd x)"
    using endpoint_after_first_crossing(1)[OF L yr] by (simp add: periodic_motion_def)
  have bounds: "-L\<le>2*L-?Y" "2*L-?Y\<le>L" "-L\<le>?Y-2*L" "?Y-2*L\<le>L"
    using L y by linarith+
  show ?thesis by (simp only: ref per bounded_position_exact[OF bounds(1,2)] bounded_position_exact[OF bounds(3,4)])
    (use L y in linarith)
qed

theorem concrete_correlation_difference:
  assumes L: "0<L" and u: "0<u"
  shows "L/2*(\<integral>x. indicator (crossing_rectangle L u) x \<partial>strip_state L)
    < (\<integral>x. bounded_position L (reflection_motion L u x)*indicator (crossing_rectangle L u) x \<partial>strip_state L)
      -(\<integral>x. bounded_position L (periodic_motion L u x)*indicator (crossing_rectangle L u) x \<partial>strip_state L)"
proof -
  interpret S: prob_space "strip_state L" by (rule strip_state_probability[OF L])
  let ?B = "indicator (crossing_rectangle L u) :: real\<times>real\<Rightarrow>real"
  have wm: "?B\<in>borel_measurable(strip_state L)" by measurable
  have wi: "integrable (strip_state L) ?B"
    by (rule S.integrable_const_bound[where B=1]) (auto simp: indicator_def intro: wm)
  have ints: "integrable (strip_state L) (\<lambda>x. bounded_position L (f x)*?B x)"
    if fm: "f\<in>measurable (strip_state L)(strip_state L)" for f
  proof (rule S.integrable_const_bound[where B=L])
    show "(\<lambda>x. bounded_position L (f x)*?B x)\<in>borel_measurable(strip_state L)"
      using fm by measurable
    show "AE x in strip_state L. norm (bounded_position L (f x)*?B x)\<le>L"
      using bounded_position_bound[OF L] L by (intro AE_I2) (auto simp: indicator_def)
  qed
  have nonneg: "AE x in strip_state L. 0\<le>?B x" by (simp add: indicator_def)
  have gap: "AE x in strip_state L. 0<?B x \<longrightarrow>
    L/2<bounded_position L (reflection_motion L u x)-bounded_position L (periodic_motion L u x)"
  proof (intro AE_I2 impI)
    fix x assume "0<?B x"
    then have "x\<in>crossing_rectangle L u" by (auto simp: indicator_def)
    show "L/2<bounded_position L (reflection_motion L u x)-bounded_position L (periodic_motion L u x)"
      by (rule crossing_observable_gap[OF L u \<open>x\<in>crossing_rectangle L u\<close>])
  qed
  have positive: "0<emeasure(strip_state L){x\<in>space(strip_state L). 0<?B x}"
    using crossing_rectangle_positive[OF L u] by (simp add: indicator_def)
  show ?thesis by (rule S.weighted_strict_gap[OF ints[OF reflection_motion_strip_measurable]
    ints[OF periodic_motion_measurable] wi nonneg gap wm positive])
qed

theorem concrete_correlations_distinct:
  assumes L: "0<L" and u: "0<u"
  shows "(\<integral>x. bounded_position L (periodic_motion L u x)*indicator (crossing_rectangle L u) x \<partial>strip_state L)
    < (\<integral>x. bounded_position L (reflection_motion L u x)*indicator (crossing_rectangle L u) x \<partial>strip_state L)"
proof -
  interpret S: prob_space "strip_state L" by (rule strip_state_probability[OF L])
  have pos: "0<measure(strip_state L)(crossing_rectangle L u)"
    using crossing_rectangle_positive[OF L u]
    by (simp add: S.emeasure_eq_measure)
  have mass: "(\<integral>x. indicator(crossing_rectangle L u) x \<partial>strip_state L)
    =measure(strip_state L)(crossing_rectangle L u)"
    by simp
  have lb: "0<L/2*measure(strip_state L)(crossing_rectangle L u)"
    using L pos by simp
  show ?thesis using concrete_correlation_difference[OF L u] lb
    by (simp only: mass; linarith)
qed

end
