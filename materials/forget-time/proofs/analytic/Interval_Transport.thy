theory Interval_Transport
  imports Circle_Measure Strip_Flow
begin

lemma interval_translation_integral:
  fixes f :: "real \<Rightarrow> ennreal"
  assumes fm[measurable]: "f\<in>borel_measurable borel"
  shows "(\<integral>\<^sup>+x. f(x+c)*indicator {a<..<b} x \<partial>lborel)
    =(\<integral>\<^sup>+y. f y*indicator {a+c<..<b+c} y \<partial>lborel)"
proof -
  have gm: "(\<lambda>y. f y*indicator {a+c<..<b+c} y)\<in>borel_measurable borel" by measurable
  have eq: "(\<integral>\<^sup>+y. f y*indicator {a+c<..<b+c} y \<partial>lborel)
    =(\<integral>\<^sup>+x. f(c+x)*indicator {a+c<..<b+c} (c+x) \<partial>lborel)"
    using nn_integral_real_affine[OF gm, of 1 c] by simp
  show ?thesis unfolding eq
    by (rule nn_integral_cong) (simp add: indicator_def add.commute)
qed

lemma interval_reflection_integral:
  fixes f :: "real \<Rightarrow> ennreal"
  assumes fm[measurable]: "f\<in>borel_measurable borel"
  shows "(\<integral>\<^sup>+x. f(c-x)*indicator {a<..<b} x \<partial>lborel)
    =(\<integral>\<^sup>+y. f y*indicator {c-b<..<c-a} y \<partial>lborel)"
proof -
  have gm: "(\<lambda>y. f y*indicator {c-b<..<c-a} y)\<in>borel_measurable borel" by measurable
  have eq: "(\<integral>\<^sup>+y. f y*indicator {c-b<..<c-a} y \<partial>lborel)
    =(\<integral>\<^sup>+x. f(c-x)*indicator {c-b<..<c-a} (c-x) \<partial>lborel)"
    using nn_integral_real_affine[OF gm, of "-1" c] by simp
  show ?thesis unfolding eq
    by (rule nn_integral_cong) (simp add: indicator_def; smt (verit))
qed

theorem uniform_translation_integral:
  fixes f :: "real \<Rightarrow> ennreal"
  assumes fm[measurable]: "f\<in>borel_measurable borel"
    and ab: "a<b"
  shows "(\<integral>\<^sup>+x. f(x+c) \<partial>uniform_measure lborel {a<..<b})
    =(\<integral>\<^sup>+y. f y \<partial>uniform_measure lborel {a+c<..<b+c})"
  using ab by (simp add: nn_integral_uniform_measure interval_translation_integral[OF fm] emeasure_lborel_Ioo)

theorem uniform_reflection_integral:
  fixes f :: "real \<Rightarrow> ennreal"
  assumes fm[measurable]: "f\<in>borel_measurable borel"
    and ab: "a<b"
  shows "(\<integral>\<^sup>+x. f(c-x) \<partial>uniform_measure lborel {a<..<b})
    =(\<integral>\<^sup>+y. f y \<partial>uniform_measure lborel {c-b<..<c-a})"
  using ab by (simp add: nn_integral_uniform_measure interval_reflection_integral[OF fm] emeasure_lborel_Ioo)

theorem gaussian_reflection_integral:
  fixes f :: "real \<Rightarrow> ennreal"
  assumes fm[measurable]: "f\<in>borel_measurable borel"
  shows "(\<integral>\<^sup>+p. f(-p) \<partial>gaussian_state)=(\<integral>\<^sup>+p. f p \<partial>gaussian_state)"
proof -
  let ?g = "\<lambda>p. ennreal(gaussian p/sqrt pi)*f p"
  have gm: "?g\<in>borel_measurable borel" unfolding gaussian_def by measurable
  have dens[measurable]: "(\<lambda>p. ennreal(gaussian p/sqrt pi))\<in>borel_measurable lborel"
    unfolding gaussian_def by measurable
  have eq: "(\<integral>\<^sup>+p. ?g p \<partial>lborel)=(\<integral>\<^sup>+p. ?g(-p) \<partial>lborel)"
    using nn_integral_real_affine[OF gm, of "-1" 0] by simp
  show ?thesis using eq by (simp add: gaussian_state_def nn_integral_density gaussian_def)
qed

theorem gaussian_positive_half_integral:
  fixes f :: "real \<Rightarrow> ennreal"
  assumes fm[measurable]: "f\<in>borel_measurable borel"
  shows "(\<integral>\<^sup>+p. f p \<partial>gaussian_state)
    =(\<integral>\<^sup>+p. (f p+f(-p))*indicator {0<..} p \<partial>gaussian_state)"
proof -
  have fG[measurable]: "f\<in>borel_measurable gaussian_state" using fm by (simp add: gaussian_state_def)
  have Gp[measurable]: "{0<..}\<in>sets gaussian_state" by (simp add: gaussian_state_def)
  have Gn[measurable]: "{..<0}\<in>sets gaussian_state" by (simp add: gaussian_state_def)
  have fneg[measurable]: "(\<lambda>p. f(-p))\<in>borel_measurable gaussian_state"
    unfolding gaussian_state_def by measurable
  have nz: "AE p in gaussian_state. p\<noteq>0"
  proof -
    have null: "{(0::real)}\<in>null_sets lborel"
      using AE_lborel_singleton[of "0::real"]
        AE_iff_null_sets[of "{0::real}" lborel] by simp
    have "{0}\<in>null_sets gaussian_state"
      using gaussian_state_null_sets[of "{0}"] null by simp
    then show ?thesis using AE_iff_null_sets[of "{0}" gaussian_state]
      by (simp add: gaussian_state_def)
  qed
  have split: "(\<integral>\<^sup>+p. f p \<partial>gaussian_state)
    =(\<integral>\<^sup>+p. f p*indicator {0<..} p+f p*indicator {..<0} p \<partial>gaussian_state)"
    by (rule nn_integral_cong_AE) (use nz in \<open>eventually_elim; simp add: indicator_def; linarith\<close>)
  have hm[measurable]: "(\<lambda>p. f p*indicator {..<0} p)\<in>borel_measurable borel" by measurable
  have neg: "(\<integral>\<^sup>+p. f p*indicator {..<0} p \<partial>gaussian_state)
    =(\<integral>\<^sup>+p. f(-p)*indicator {0<..} p \<partial>gaussian_state)"
    using gaussian_reflection_integral[OF hm] by (simp add: indicator_def)
  have "(\<integral>\<^sup>+p. f p \<partial>gaussian_state)
    =(\<integral>\<^sup>+p. f p*indicator {0<..} p \<partial>gaussian_state)
     +(\<integral>\<^sup>+p. f p*indicator {..<0} p \<partial>gaussian_state)"
    using split by (simp add: nn_integral_add)
  also have "...=(\<integral>\<^sup>+p. f p*indicator {0<..} p \<partial>gaussian_state)
     +(\<integral>\<^sup>+p. f(-p)*indicator {0<..} p \<partial>gaussian_state)"
    by (simp only: neg)
  also have "...=(\<integral>\<^sup>+p. (f p+f(-p))*indicator {0<..} p \<partial>gaussian_state)"
    by (simp add: nn_integral_add distrib_right)
  finally show ?thesis .
qed

theorem uniform_equal_halves:
  fixes f :: "real \<Rightarrow> ennreal"
  assumes fm[measurable]: "f\<in>borel_measurable borel" and L: "0<L"
  shows "(\<integral>\<^sup>+y. f y \<partial>uniform_measure lborel {0<..<2*L})
    +(\<integral>\<^sup>+y. f y \<partial>uniform_measure lborel {2*L<..<4*L})
    =2*(\<integral>\<^sup>+y. f y \<partial>uniform_measure lborel {0<..<4*L})"
proof -
  let ?J = "\<integral>\<^sup>+y. f y*indicator {0<..<4*L} y \<partial>lborel"
  have sum: "(\<integral>\<^sup>+y. f y*indicator {0<..<2*L} y \<partial>lborel)
    +(\<integral>\<^sup>+y. f y*indicator {2*L<..<4*L} y \<partial>lborel)=?J"
  proof -
    have ae: "AE y in lborel. f y*indicator {0<..<2*L} y+f y*indicator {2*L<..<4*L} y
      =f y*indicator {0<..<4*L} y"
      using AE_lborel_singleton[of "2*L"]
      by eventually_elim (use L in \<open>auto simp: indicator_def; linarith\<close>)
    show ?thesis using nn_integral_cong_AE[OF ae] by (simp add: nn_integral_add)
  qed
  have scale: "(1::ennreal)/ennreal(2*L)=2/ennreal(4*L)"
  proof -
    have a: "ennreal (1::real)/ennreal(2*L)=ennreal(1/(2*L))"
      by (rule divide_ennreal) (use L in auto)
    have b: "ennreal (2::real)/ennreal(4*L)=ennreal(2/(4*L))"
      by (rule divide_ennreal) (use L in auto)
    show ?thesis using a b by simp
  qed
  have den1: "emeasure lborel {0<..<2*L}=ennreal(2*L)" using L by simp
  have den2: "emeasure lborel {2*L<..<4*L}=ennreal(2*L)" using L by simp
  have den4: "emeasure lborel {0<..<4*L}=ennreal(4*L)" using L by simp
  have algebra: "?J/ennreal(2*L)=2*(?J/ennreal(4*L))"
  proof -
    have "?J/ennreal(2*L)=?J*((1::ennreal)/ennreal(2*L))" by (simp add: divide_ennreal_def)
    also have "...=2*(?J/ennreal(4*L))" by (simp only: scale) (simp add: divide_ennreal_def ac_simps)
    finally show ?thesis .
  qed
  show ?thesis
    by (simp add: nn_integral_uniform_measure den1 den2 den4
      add_divide_distrib_ennreal[symmetric] sum algebra)
qed

end
