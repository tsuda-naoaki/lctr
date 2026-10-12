theory Strip_Flow
  imports Gaussian_Strip
begin

definition gaussian_state :: "real measure" where
  "gaussian_state = density lborel (\<lambda>p. ennreal (gaussian p / sqrt pi))"

definition strip_state :: "real \<Rightarrow> (real \<times> real) measure" where
  "strip_state L = uniform_measure lborel {-L<..<L} \<Otimes>\<^sub>M gaussian_state"

definition strip_domain :: "real \<Rightarrow> real \<Rightarrow> (real \<times> real) set" where
  "strip_domain L u = {(Q,P). -L < Q \<and> Q < L \<and> -L < Q+2*P*u \<and> Q+2*P*u < L}"

definition strip_flow :: "real \<Rightarrow> real \<Rightarrow> real \<times> real \<Rightarrow> (real \<times> real) option" where
  "strip_flow L u s = (if s \<in> strip_domain L u then Some (fst s + 2 * snd s * u, snd s) else None)"

lemma gaussian_state_probability:
  "prob_space gaussian_state"
proof -
  have h: "has_bochner_integral lborel (\<lambda>p. gaussian p / sqrt pi) 1"
    using has_bochner_integral_divide[OF gaussian_integral, of "sqrt pi"] by simp
  have nn: "(\<integral>\<^sup>+p. ennreal (gaussian p / sqrt pi) \<partial>lborel) = 1"
  proof -
    have pos: "AE p in lborel. 0 \<le> gaussian p / sqrt pi"
      by (simp add: gaussian_def)
    show ?thesis using nn_integral_eq_integral[OF integrable.intros[OF h] pos]
      by (simp only: has_bochner_integral_integral_eq[OF h] ennreal_1)
  qed
  have fm[measurable]: "(\<lambda>p. ennreal (gaussian p / sqrt pi)) \<in> borel_measurable lborel"
    unfolding gaussian_def by measurable
  show ?thesis
  proof
    show "emeasure gaussian_state (space gaussian_state) = 1"
      unfolding gaussian_state_def by (simp add: emeasure_density nn fm)
  qed
qed

lemma gaussian_state_null_sets:
  assumes "A \<in> sets lborel"
  shows "A \<in> null_sets gaussian_state \<longleftrightarrow> A \<in> null_sets lborel"
proof -
  have fm: "(\<lambda>p. ennreal (gaussian p / sqrt pi)) \<in> borel_measurable lborel"
    unfolding gaussian_def by measurable
  have Ab: "A \<in> sets borel" using assms by simp
  have an: "(AE x in lborel. x \<notin> A) \<longleftrightarrow> A \<in> null_sets lborel"
    using AE_iff_null_sets[OF assms] by blast
  show ?thesis
    unfolding gaussian_state_def
    apply (subst null_sets_density_iff[OF fm])
    apply (simp add: gaussian_def Ab an)
    done
qed

lemma gaussian_interval_positive:
  assumes "a < b"
  shows "0 < emeasure gaussian_state {a<..<b}"
proof -
  have "{a<..<b} \<notin> null_sets lborel" using assms by (simp add: null_sets_def)
  then have "{a<..<b} \<notin> null_sets gaussian_state"
    using gaussian_state_null_sets[of "{a<..<b}"] by simp
  then show ?thesis by (simp add: null_sets_def gaussian_state_def zero_less_iff_neq_zero)
qed

lemma strip_state_probability:
  assumes "0 < L"
  shows "prob_space (strip_state L)"
proof -
  interpret G: prob_space gaussian_state by (rule gaussian_state_probability)
  interpret U: prob_space "uniform_measure lborel {-L<..<L}"
    by (rule prob_space_uniform_measure) (use assms in auto)
  interpret P: pair_prob_space "uniform_measure lborel {-L<..<L}" gaussian_state
    by unfold_locales
  show ?thesis unfolding strip_state_def by (rule P.prob_space_axioms)
qed

lemma strip_rectangle_positive:
  assumes "0 < L" "a < b"
  shows "0 < emeasure (strip_state L) ({0<..<L} \<times> {a<..<b})"
proof -
  interpret G: prob_space gaussian_state by (rule gaussian_state_probability)
  have gp: "0 < emeasure gaussian_state {a<..<b}"
    by (rule gaussian_interval_positive[OF assms(2)])
  have U: "0 < emeasure (uniform_measure lborel {-L<..<L}) {0<..<L}"
  proof -
    have inter: "{-L<..<L} \<inter> {0<..<L} = {0<..<L}"
      using assms(1) by auto
    show ?thesis using assms(1)
      by (simp add: inter ennreal_zero_less_divide)
  qed
  show ?thesis unfolding strip_state_def
    using U gp
    by (subst G.emeasure_pair_measure_Times)
      (auto simp: gaussian_state_def ennreal_zero_less_mult_iff)
qed

lemma strip_state_space [simp]: "space (strip_state L) = UNIV"
  by (simp add: strip_state_def gaussian_state_def space_pair_measure)

lemma strip_state_sets [simp]: "sets (strip_state L) = sets (lborel \<Otimes>\<^sub>M lborel)"
  by (simp add: strip_state_def gaussian_state_def sets_pair_measure)

lemma strip_domain_measurable [measurable]: "strip_domain L u \<in> sets (strip_state L)"
proof -
  have eq: "strip_domain L u = {s. -L<fst s \<and> fst s<L \<and>
    -L<fst s + 2 * snd s*u \<and> fst s + 2 * snd s*u<L}"
    by (auto simp: strip_domain_def)
  show ?thesis
    unfolding eq strip_state_sets
    apply (subst sets_pair_measure_cong[OF sets_lborel sets_lborel])
    apply (subst borel_prod)
    apply (rule borel_open)
    apply (intro open_Collect_conj open_Collect_less continuous_intros)
    done
qed

lemma positive_escape_rectangle:
  assumes "0 < L" "0 < u"
  shows "({0<..<L} \<times> {L/u<..<L/u+1}) \<subseteq> - strip_domain L u"
proof
  fix s assume s: "s \<in> {0<..<L} \<times> {L/u<..<L/u+1}"
  obtain Q P where sp: "s=(Q,P)" by (cases s) auto
  have q: "0<Q" and p: "L/u<P" using s by (simp_all add: sp)
  have "L<P*u" using p assms(2) by (simp add: divide_less_eq)
  then have "L<Q+2*P*u" using q assms(1) by linarith
  then show "s \<in> - strip_domain L u" by (simp add: sp strip_domain_def)
qed

lemma negative_escape_rectangle:
  assumes "0 < L" "u < 0"
  shows "({0<..<L} \<times> {L/u-1<..<L/u}) \<subseteq> - strip_domain L u"
proof
  fix s assume s: "s \<in> {0<..<L} \<times> {L/u-1<..<L/u}"
  obtain Q P where sp: "s=(Q,P)" by (cases s) auto
  have q: "0<Q" and p: "P<L/u" using s by (simp_all add: sp)
  have "L<P*u" using p assms(2) by (simp add: less_divide_eq)
  then have "L<Q+2*P*u" using q assms(1) by linarith
  then show "s \<in> - strip_domain L u" by (simp add: sp strip_domain_def)
qed

theorem strip_undefined_positive_probability:
  assumes "0 < L" "u \<noteq> 0"
  shows "0 < emeasure (strip_state L) {s. strip_flow L u s = None}"
proof -
  have eq: "{s. strip_flow L u s = None} = - strip_domain L u"
    by (auto simp: strip_flow_def)
  have cm: "- strip_domain L u \<in> sets (strip_state L)"
    using sets.Diff[OF sets.top strip_domain_measurable[of L u]]
    by (simp only: strip_state_space Compl_eq_Diff_UNIV)
  show ?thesis
  proof (cases "0<u")
    case True
    have pos: "0 < emeasure (strip_state L) ({0<..<L} \<times> {L/u<..<L/u+1})"
      by (rule strip_rectangle_positive[OF assms(1)]) simp
    have le: "emeasure (strip_state L) ({0<..<L} \<times> {L/u<..<L/u+1})
      \<le> emeasure (strip_state L) (- strip_domain L u)"
      by (rule emeasure_mono[OF positive_escape_rectangle[OF assms(1) True] cm])
    show ?thesis unfolding eq by (rule less_le_trans[OF pos le])
  next
    case False
    have neg: "u<0" using False assms(2) by linarith
    have pos: "0 < emeasure (strip_state L) ({0<..<L} \<times> {L/u-1<..<L/u})"
      by (rule strip_rectangle_positive[OF assms(1)]) simp
    have le: "emeasure (strip_state L) ({0<..<L} \<times> {L/u-1<..<L/u})
      \<le> emeasure (strip_state L) (- strip_domain L u)"
      by (rule emeasure_mono[OF negative_escape_rectangle[OF assms(1) neg] cm])
    show ?thesis unfolding eq by (rule less_le_trans[OF pos le])
  qed
qed

corollary rescaled_strip_undefined:
  assumes "0<L" "a\<noteq>0" "u\<noteq>0"
  shows "0 < emeasure (strip_state L) {s. strip_flow L (a*u) s = None}"
  by (rule strip_undefined_positive_probability[OF assms(1)]) (use assms in simp)

end
