theory Reflection_Group
  imports Reflection_Measure Circle_Open_Measure
begin

theorem reflection_unfolded_inverse:
  assumes L: "0<L"
  shows "AE z in unfolded_state L. reflection_unfold L (reflection_fold L z)=z"
proof -
  let ?V = "uniform_measure lborel {0<..<4*L}"
  interpret S: prob_space speed_state by (rule speed_state_probability)
  interpret V: prob_space ?V by (rule prob_space_uniform_measure) (use L in auto)
  interpret SV: pair_sigma_finite speed_state ?V by unfold_locales
  have am: "abs\<in>measurable gaussian_state lborel" by (simp add: gaussian_state_def)
  have pos: "AE s in speed_state. 0<s"
  proof -
    have ap: "AE p in gaussian_state. 0<abs p" using gaussian_nonzero by eventually_elim simp
    show ?thesis unfolding speed_state_def
      by (subst AE_distr_iff[OF am]) (simp_all add: gaussian_nonzero)
  qed
  have vy: "AE y in ?V. 0<y \<and> y<4*L \<and> y\<noteq>2*L"
    by (rule AE_uniform_measureI) (simp, use AE_lborel_singleton[of "2*L"] in \<open>eventually_elim; auto\<close>)
  have nested: "AE s in speed_state. AE y in ?V. 0<s \<and> 0<y \<and> y<4*L \<and> y\<noteq>2*L"
    using pos by eventually_elim (use vy in \<open>eventually_elim; simp\<close>)
  have meas: "{z\<in>space(speed_state\<Otimes>\<^sub>M ?V). 0<fst z \<and> 0<snd z \<and> snd z<4*L \<and> snd z\<noteq>2*L}
    \<in>sets(speed_state\<Otimes>\<^sub>M ?V)"
    unfolding speed_state_def by measurable
  have good: "AE z in unfolded_state L. 0<fst z \<and> 0<snd z \<and> snd z<4*L \<and> snd z\<noteq>2*L"
    unfolding unfolded_state_def by (rule SV.AE_pair_measure[OF meas]) (use nested in simp)
  show ?thesis using good by eventually_elim
    (metis prod.collapse reflection_unfold_fold)
qed

theorem reflection_preserves_state:
  assumes L: "0<L"
  shows "distr (strip_state L) (strip_state L) (reflection_motion L u)=strip_state L"
proof -
  let ?M = "strip_state L"
  let ?N = "unfolded_state L"
  let ?U = "reflection_unfold L"
  let ?F = "reflection_fold L"
  let ?H = "\<lambda>(s,y). (s,circle_motion (4*L) (2 * s) u y)"
  have um: "?U\<in>measurable ?M ?N" using reflection_maps_measurable(1)[of L]
    by (simp only: measurable_cong_sets[OF strip_state_sets unfolded_state_sets])
  have fm: "?F\<in>measurable ?N ?M" using reflection_maps_measurable(2)[of L]
    by (simp only: measurable_cong_sets[OF unfolded_state_sets strip_state_sets])
  have hm: "?H\<in>measurable ?N ?N"
    unfolding unfolded_state_def speed_state_def circle_motion_def wrap_def frac_def by measurable
  have v: "(\<lambda>s. 2 * s)\<in>borel_measurable speed_state" by (simp add: speed_state_def)
  have inv: "distr ?N ?N ?H=?N"
    unfolding unfolded_state_def
    by (rule circle_skew_motion_preserves_open_product[OF _ v]) (use L in simp)
  have eq: "?F \<circ> ?H \<circ> ?U=reflection_motion L u"
    by (rule ext) (simp add: o_def reflection_motion_def split: prod.splits)
  show ?thesis using transported_invariant_measure[OF um fm hm
    reflection_unfold_pushforward[OF L] reflection_fold_pushforward[OF L] inv]
    by (simp only: eq)
qed

theorem reflection_group_law:
  assumes L: "0<L"
  shows "AE x in strip_state L. reflection_motion L u (reflection_motion L t x)=reflection_motion L (u+t) x"
proof -
  let ?M = "strip_state L"
  let ?N = "unfolded_state L"
  let ?U = "reflection_unfold L"
  let ?F = "reflection_fold L"
  let ?H = "\<lambda>t. \<lambda>(s,y). (s,circle_motion (4*L) (2 * s) t y)"
  have um: "?U\<in>measurable ?M ?N" using reflection_maps_measurable(1)[of L]
    by (simp only: measurable_cong_sets[OF strip_state_sets unfolded_state_sets])
  have hm: "?H t\<in>measurable ?N ?N" for t
    unfolding unfolded_state_def speed_state_def circle_motion_def wrap_def frac_def by measurable
  have v: "(\<lambda>s. 2 * s)\<in>borel_measurable speed_state" by (simp add: speed_state_def)
  have inv: "distr ?N ?N (?H t)=?N" for t
    unfolding unfolded_state_def
    by (rule circle_skew_motion_preserves_open_product[OF _ v]) (use L in simp)
  have grp: "AE z in ?N. ?H u (?H t z)=?H (u+t) z"
    by (intro AE_I2 circle_skew_composition) (use L in simp)
  have eq: "?F(?H t (?U x))=reflection_motion L t x" for t x
    by (simp add: reflection_motion_def split: prod.splits)
  show ?thesis using transported_group_law[OF um hm reflection_unfold_pushforward[OF L]
    inv reflection_unfolded_inverse[OF L] grp] by (simp only: eq)
qed

theorem reflection_identity:
  assumes L: "0<L"
  shows "AE x in strip_state L. reflection_motion L 0 x=x"
proof -
  let ?M = "strip_state L"
  let ?N = "unfolded_state L"
  let ?H = "\<lambda>(s,y). (s,circle_motion (4*L) (2 * s) 0 y)"
  interpret S: prob_space speed_state by (rule speed_state_probability)
  have um: "reflection_unfold L\<in>measurable ?M ?N" using reflection_maps_measurable(1)[of L]
    by (simp only: measurable_cong_sets[OF strip_state_sets unfolded_state_sets])
  have zero: "AE z in ?N. ?H z=z"
    unfolding unfolded_state_def by (rule circle_skew_identity[OF _ S.sigma_finite_measure_axioms]) (use L in simp)
  have eq: "reflection_fold L (?H (reflection_unfold L x))=reflection_motion L 0 x" for x
    by (simp add: reflection_motion_def split: prod.splits)
  show ?thesis using transported_identity[OF um reflection_unfold_pushforward[OF L]
    zero reflection_original_inverse[OF L]] by (simp only: eq)
qed

end
