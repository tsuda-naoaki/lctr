theory Reflection_Measure
  imports Reflection_Completion Interval_Transport Completion_Conjugacy
begin

definition speed_state :: "real measure" where
  "speed_state=distr gaussian_state lborel abs"

definition unfolded_state :: "real \<Rightarrow> (real\<times>real) measure" where
  "unfolded_state L=speed_state\<Otimes>\<^sub>M uniform_measure lborel {0<..<4*L}"

lemma speed_state_probability: "prob_space speed_state"
proof -
  interpret G: prob_space gaussian_state by (rule gaussian_state_probability)
  show ?thesis unfolding speed_state_def
    by (rule G.prob_space_distr) (simp add: gaussian_state_def)
qed

lemma unfolded_state_probability:
  assumes "0<L"
  shows "prob_space(unfolded_state L)"
proof -
  interpret S: prob_space speed_state by (rule speed_state_probability)
  interpret U: prob_space "uniform_measure lborel {0<..<4*L}"
    by (rule prob_space_uniform_measure) (use assms in auto)
  interpret SU: pair_prob_space speed_state "uniform_measure lborel {0<..<4*L}" by unfold_locales
  show ?thesis unfolding unfolded_state_def by (rule SU.prob_space_axioms)
qed

theorem reflection_unfold_integral:
  fixes f :: "real\<times>real \<Rightarrow> ennreal"
  assumes L: "0<L" and fm[measurable]: "f\<in>borel_measurable (lborel\<Otimes>\<^sub>M lborel)"
  shows "(\<integral>\<^sup>+x. f(reflection_unfold L x) \<partial>strip_state L)
    =(\<integral>\<^sup>+z. f z \<partial>unfolded_state L)"
proof -
  let ?U = "uniform_measure lborel {-L<..<L}"
  let ?V = "uniform_measure lborel {0<..<4*L}"
  let ?h = "\<lambda>p. \<integral>\<^sup>+q. f(abs p,if 0<p then q+L else 3*L-q) \<partial>?U"
  let ?k = "\<lambda>p. \<integral>\<^sup>+y. f(abs p,y) \<partial>?V"
  interpret U: prob_space ?U by (rule prob_space_uniform_measure) (use L in auto)
  interpret V: prob_space ?V by (rule prob_space_uniform_measure) (use L in auto)
  interpret G: prob_space gaussian_state by (rule gaussian_state_probability)
  interpret UG: pair_sigma_finite ?U gaussian_state by unfold_locales
  have fmB[measurable]: "f\<in>borel_measurable (borel\<Otimes>\<^sub>M borel)"
    using fm by (simp add: sets_pair_measure)
  have slice[measurable]: "(\<lambda>y. f(s,y))\<in>borel_measurable borel" for s
    by (rule measurable_compose_Pair1[OF _ fmB]) simp
  have hm[measurable]: "?h\<in>borel_measurable borel"
    by (rule U.borel_measurable_nn_integral) measurable
  have km[measurable]: "?k\<in>borel_measurable borel"
    by (rule V.borel_measurable_nn_integral) measurable
  have halves: "?h p+?h(-p)=2*?k p" if "0<p" for p
  proof -
    have plus: "?h p=(\<integral>\<^sup>+y. f(p,y) \<partial>uniform_measure lborel {0<..<2*L})"
      using uniform_translation_integral[OF slice[of p], where a="-L" and b=L and c=L] L that
      by (simp add: abs_of_pos)
    have minus: "?h(-p)=(\<integral>\<^sup>+y. f(p,y) \<partial>uniform_measure lborel {2*L<..<4*L})"
      using uniform_reflection_integral[OF slice[of p], where a="-L" and b=L and c="3*L"] L that
      by (simp add: abs_of_pos)
    show ?thesis
      by (simp only: plus minus)
        (use uniform_equal_halves[OF slice[of p] L] that in \<open>simp add: abs_of_pos\<close>)
  qed
  have outer: "(\<integral>\<^sup>+p. ?h p \<partial>gaussian_state)
    =(\<integral>\<^sup>+p. ?k p \<partial>gaussian_state)"
    unfolding gaussian_positive_half_integral[OF hm] gaussian_positive_half_integral[OF km]
  proof (rule nn_integral_cong)
    fix p assume "p\<in>space gaussian_state"
    show "(?h p+?h(-p))*indicator {0<..} p=(?k p+?k(-p))*indicator {0<..} p"
    proof (cases "0<p")
      case True
      then show ?thesis using halves[OF True] by (simp add: indicator_def mult_2)
    next
      case False then show ?thesis by (simp add: indicator_def)
    qed
  qed
  have um: "reflection_unfold L\<in>measurable (strip_state L) (lborel\<Otimes>\<^sub>M lborel)"
    using reflection_maps_measurable(1)[of L]
    by (simp add: measurable_def strip_state_def gaussian_state_def space_pair_measure sets_pair_measure)
  have comp[measurable]: "(\<lambda>x. f(reflection_unfold L x))\<in>borel_measurable (strip_state L)"
    by (rule measurable_compose[OF um fm])
  have pairf[measurable]: "f\<in>borel_measurable (speed_state\<Otimes>\<^sub>M ?V)"
    using fm by (simp add: speed_state_def sets_pair_measure)
  have inner[measurable]: "(\<lambda>s. \<integral>\<^sup>+y. f(s,y) \<partial>?V)\<in>borel_measurable lborel"
    by (rule V.borel_measurable_nn_integral) (use fm in \<open>simp add: sets_pair_measure\<close>)
  have am: "abs\<in>measurable gaussian_state lborel" by (simp add: gaussian_state_def)
  have compU: "(\<lambda>x. f(reflection_unfold L x))\<in>borel_measurable (?U\<Otimes>\<^sub>M gaussian_state)"
    using comp by (simp only: strip_state_def)
  have "(\<integral>\<^sup>+x. f(reflection_unfold L x) \<partial>strip_state L)
    =(\<integral>\<^sup>+p. ?h p \<partial>gaussian_state)"
    using UG.nn_integral_snd[OF compU]
    by (simp only: strip_state_def reflection_unfold_def fst_conv snd_conv)
  also have "...=(\<integral>\<^sup>+p. ?k p \<partial>gaussian_state)" by (rule outer)
  also have "...=(\<integral>\<^sup>+s. \<integral>\<^sup>+y. f(s,y) \<partial>?V \<partial>speed_state)"
    unfolding speed_state_def by (simp add: nn_integral_distr[OF am])
  also have "...=(\<integral>\<^sup>+z. f z \<partial>unfolded_state L)"
    unfolding unfolded_state_def by (rule V.nn_integral_fst[OF pairf])
  finally show ?thesis .
qed

lemma unfolded_state_sets[simp]:
  "sets(unfolded_state L)=sets(lborel\<Otimes>\<^sub>M lborel)"
  by (simp add: unfolded_state_def speed_state_def sets_pair_measure)

lemma unfolded_state_space[simp]: "space(unfolded_state L)=UNIV"
  by (simp add: unfolded_state_def speed_state_def space_pair_measure)

theorem reflection_unfold_pushforward:
  assumes L: "0<L"
  shows "distr (strip_state L) (unfolded_state L) (reflection_unfold L)=unfolded_state L"
proof (rule measure_eqI)
  let ?M = "strip_state L"
  let ?N = "unfolded_state L"
  have um: "reflection_unfold L\<in>measurable ?M ?N"
    using reflection_maps_measurable(1)[of L]
    by (simp only: measurable_cong_sets[OF strip_state_sets unfolded_state_sets])
  show "sets(distr ?M ?N (reflection_unfold L))=sets ?N" by simp
  fix A assume Am: "A\<in>sets(distr ?M ?N (reflection_unfold L))"
  then have Ab[measurable]: "A\<in>sets(lborel\<Otimes>\<^sub>M lborel)" by simp
  have im[measurable]: "(indicator A :: real\<times>real\<Rightarrow>ennreal)\<in>borel_measurable (lborel\<Otimes>\<^sub>M lborel)" by measurable
  have idm: "(indicator A :: real\<times>real\<Rightarrow>ennreal)\<in>borel_measurable(distr ?M ?N (reflection_unfold L))"
    using im by (simp add: measurable_def unfolded_state_def speed_state_def space_pair_measure sets_pair_measure)
  have An: "A\<in>sets ?N" using Am by simp
  show "emeasure(distr ?M ?N (reflection_unfold L)) A=emeasure ?N A"
    using reflection_unfold_integral[OF L im] nn_integral_distr[OF um idm]
    by (simp only: nn_integral_indicator[OF Am] nn_integral_indicator[OF An])
qed

lemma gaussian_nonzero:
  "AE p in gaussian_state. p\<noteq>0"
proof -
  have n: "{(0::real)}\<in>null_sets lborel"
    using AE_lborel_singleton[of "0::real"] AE_iff_null_sets[of "{0::real}" lborel] by simp
  have "{(0::real)}\<in>null_sets gaussian_state"
    using gaussian_state_null_sets[of "{0}"] n by simp
  then show ?thesis using AE_iff_null_sets[of "{0}" gaussian_state]
    by (simp add: gaussian_state_def)
qed

theorem reflection_original_inverse:
  assumes L: "0<L"
  shows "AE x in strip_state L. reflection_fold L (reflection_unfold L x)=x"
proof -
  let ?U = "uniform_measure lborel {-L<..<L}"
  interpret U: prob_space ?U by (rule prob_space_uniform_measure) (use L in auto)
  interpret G: prob_space gaussian_state by (rule gaussian_state_probability)
  interpret UG: pair_sigma_finite ?U gaussian_state by unfold_locales
  have qu: "AE q in ?U. -L<q \<and> q<L"
    by (rule AE_uniform_measureI) auto
  have nested: "AE q in ?U. AE p in gaussian_state. -L<q \<and> q<L \<and> p\<noteq>0"
    using qu by eventually_elim
      (use gaussian_nonzero in \<open>eventually_elim; simp\<close>)
  have meas: "{x\<in>space (?U\<Otimes>\<^sub>M gaussian_state). -L<fst x \<and> fst x<L \<and> snd x\<noteq>0}
    \<in>sets(?U\<Otimes>\<^sub>M gaussian_state)"
    unfolding gaussian_state_def by measurable
  have good: "AE x in strip_state L. -L<fst x \<and> fst x<L \<and> snd x\<noteq>0"
    unfolding strip_state_def by (rule UG.AE_pair_measure[OF meas]) (use nested in simp)
  show ?thesis using good by eventually_elim
    (metis prod.collapse reflection_fold_unfold)
qed

theorem reflection_fold_pushforward:
  assumes L: "0<L"
  shows "distr (unfolded_state L) (strip_state L) (reflection_fold L)=strip_state L"
proof -
  let ?M = "strip_state L"
  let ?N = "unfolded_state L"
  let ?U = "reflection_unfold L"
  let ?F = "reflection_fold L"
  have um: "?U\<in>measurable ?M ?N" using reflection_maps_measurable(1)[of L]
    by (simp only: measurable_cong_sets[OF strip_state_sets unfolded_state_sets])
  have fm: "?F\<in>measurable ?N ?M" using reflection_maps_measurable(2)[of L]
    by (simp only: measurable_cong_sets[OF unfolded_state_sets strip_state_sets])
  have cm: "?F \<circ> ?U\<in>measurable ?M ?M" by (rule measurable_comp[OF um fm])
  have id: "distr ?M ?M (?F \<circ> ?U)=distr ?M ?M (\<lambda>x. x)"
    by (rule distr_cong_AE[OF refl refl _ cm])
      (use reflection_original_inverse[OF L] in \<open>simp add: o_def\<close>, simp)
  show ?thesis using distr_distr[OF fm um] reflection_unfold_pushforward[OF L] id by simp
qed

end
