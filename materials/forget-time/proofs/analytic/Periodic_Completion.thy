theory Periodic_Completion
  imports Reflection_Group
begin

lemma uniform_translation_pushforward:
  fixes a b c :: real
  assumes ab: "a<b"
  shows "distr (uniform_measure lborel {a<..<b})
    (uniform_measure lborel {a+c<..<b+c}) (\<lambda>x. x+c)
    =uniform_measure lborel {a+c<..<b+c}"
proof (rule measure_eqI)
  show "sets(distr (uniform_measure lborel {a<..<b})
    (uniform_measure lborel {a+c<..<b+c}) (\<lambda>x. x+c))
    =sets(uniform_measure lborel {a+c<..<b+c})" by simp
  fix A assume A: "A\<in>sets(distr (uniform_measure lborel {a<..<b})
    (uniform_measure lborel {a+c<..<b+c}) (\<lambda>x. x+c))"
  have am[measurable]: "A\<in>sets borel" using A by simp
  have sm: "(\<lambda>x. x+c)\<in>measurable (uniform_measure lborel {a<..<b})
    (uniform_measure lborel {a+c<..<b+c})" by measurable
  have im: "(indicator A :: real\<Rightarrow>ennreal)\<in>borel_measurable
    (distr (uniform_measure lborel {a<..<b}) (uniform_measure lborel {a+c<..<b+c}) (\<lambda>x. x+c))"
    by measurable
  have eq: "(\<integral>\<^sup>+x. indicator A (x+c) \<partial>uniform_measure lborel {a<..<b})
    =(\<integral>\<^sup>+y. indicator A y \<partial>uniform_measure lborel {a+c<..<b+c})"
    by (rule uniform_translation_integral[OF _ ab]) measurable
  show "emeasure (distr (uniform_measure lborel {a<..<b})
    (uniform_measure lborel {a+c<..<b+c}) (\<lambda>x. x+c)) A
    =emeasure (uniform_measure lborel {a+c<..<b+c}) A"
    using eq nn_integral_distr[OF sm im]
    by (simp only: nn_integral_indicator[OF A] nn_integral_indicator[of A "uniform_measure lborel {a+c<..<b+c}"] sets_uniform_measure am sets_lborel)
qed

definition periodic_unfold :: "real \<Rightarrow> real\<times>real \<Rightarrow> real\<times>real" where
  "periodic_unfold L x=(snd x,fst x+L)"
definition periodic_fold :: "real \<Rightarrow> real\<times>real \<Rightarrow> real\<times>real" where
  "periodic_fold L z=(snd z-L,fst z)"
definition periodic_motion :: "real \<Rightarrow> real \<Rightarrow> real\<times>real \<Rightarrow> real\<times>real" where
  "periodic_motion L u x=(periodic_position L (fst x+2 * snd x*u),snd x)"
definition periodic_state :: "real \<Rightarrow> (real\<times>real) measure" where
  "periodic_state L=gaussian_state\<Otimes>\<^sub>M uniform_measure lborel {0<..<2*L}"

lemma periodic_state_sets[simp]: "sets(periodic_state L)=sets(lborel\<Otimes>\<^sub>M lborel)"
  by (simp add: periodic_state_def gaussian_state_def sets_pair_measure)

lemma periodic_maps[measurable]:
  "periodic_unfold L\<in>measurable (strip_state L) (periodic_state L)"
  "periodic_fold L\<in>measurable (periodic_state L) (strip_state L)"
  unfolding periodic_unfold_def periodic_fold_def periodic_state_def strip_state_def gaussian_state_def
  by (measurable, measurable)

lemma periodic_inverses:
  "periodic_fold L (periodic_unfold L x)=x"
  "periodic_unfold L (periodic_fold L x)=x"
  by (simp_all add: periodic_fold_def periodic_unfold_def)

theorem periodic_unfold_pushforward:
  assumes L: "0<L"
  shows "distr (strip_state L) (periodic_state L) (periodic_unfold L)=periodic_state L"
proof -
  let ?U = "uniform_measure lborel {-L<..<L}"
  let ?V = "uniform_measure lborel {0<..<2*L}"
  let ?G = gaussian_state
  interpret G: prob_space ?G by (rule gaussian_state_probability)
  interpret V: prob_space ?V by (rule prob_space_uniform_measure) (use L in auto)
  interpret GV: pair_sigma_finite ?G ?V by unfold_locales
  have shift: "distr ?U ?V (\<lambda>x. x+L)=?V"
    using uniform_translation_pushforward[of "-L" L L] L by simp
  have sm: "(\<lambda>x. x+L)\<in>measurable ?U ?V" by measurable
  have id: "distr ?G ?G (\<lambda>x. x)=?G" by simp
  have pair: "distr (?U\<Otimes>\<^sub>M ?G) (?V\<Otimes>\<^sub>M ?G) (\<lambda>(x,y). (x+L,y))=?V\<Otimes>\<^sub>M ?G"
    using pair_measure_distr[OF sm measurable_ident, of ?G] G.sigma_finite_measure_axioms
    by (simp add: shift id_def)
  have pm: "(\<lambda>(x,y). (x+L,y))\<in>measurable (?U\<Otimes>\<^sub>M ?G) (?V\<Otimes>\<^sub>M ?G)" by measurable
  have swap: "distr (?V\<Otimes>\<^sub>M ?G) (?G\<Otimes>\<^sub>M ?V) (\<lambda>(x,y). (y,x))=?G\<Otimes>\<^sub>M ?V"
    by (rule GV.distr_pair_swap[symmetric])
  have comp: "(\<lambda>(x,y). (y,x)) \<circ> (\<lambda>(x,y). (x+L,y))=periodic_unfold L"
    by (rule ext) (simp add: o_def periodic_unfold_def split: prod.splits)
  show ?thesis unfolding strip_state_def periodic_state_def
    using distr_distr[OF measurable_pair_swap' pm] pair swap by (simp only: comp)
qed

theorem periodic_fold_pushforward:
  assumes L: "0<L"
  shows "distr (periodic_state L) (strip_state L) (periodic_fold L)=strip_state L"
proof -
  have eq: "periodic_fold L \<circ> periodic_unfold L=(\<lambda>x. x)"
    by (rule ext) (simp add: periodic_inverses)
  show ?thesis using distr_distr[OF periodic_maps(2,1), of L]
    periodic_unfold_pushforward[OF L] by (simp add: eq)
qed

end
