theory Circle_Measure
  imports "HOL-Probability.Probability" "Thermal_Logical_Core.Endpoint_Completions"
begin

lemma wrap_measurable[measurable]:
  "wrap w \<in> borel_measurable borel"
  unfolding wrap_def frac_def by measurable

lemma translation_emeasure:
  fixes A :: "real set"
  assumes A: "A\<in>sets borel"
  shows "emeasure lborel ((\<lambda>x. r+x) -` A)=emeasure lborel A"
proof -
  have eq: "lborel=distr lborel borel (\<lambda>x. r+x)"
    using lborel_real_affine[of "1::real" r] by (simp add: density_1)
  show ?thesis using emeasure_distr[of "\<lambda>x. r+x" lborel borel A] A eq
    by (simp add: space_lborel)
qed

lemma wrap_translation_emeasure:
  fixes w r :: real and A :: "real set"
  assumes w: "0<w" and r: "0\<le>r" "r<w" and A: "A\<in>sets borel"
  shows "emeasure lborel ({0..<w}\<inter>(\<lambda>x. wrap w (x+r)) -` A)
    =emeasure lborel ({0..<w}\<inter>A)"
proof -
  let ?U = "A\<inter>{r..<w}"
  let ?V = "A\<inter>{0..<r}"
  let ?S = "(\<lambda>x. r+x) -` ?U"
  let ?T = "(\<lambda>x. (r-w)+x) -` ?V"
  have U[measurable]: "?U\<in>sets borel" using A by measurable
  have V[measurable]: "?V\<in>sets borel" using A by measurable
  have S[measurable]: "?S\<in>sets lborel"
    using measurable_sets[of "\<lambda>x. r+x" lborel borel ?U] U by (simp add: space_lborel)
  have T[measurable]: "?T\<in>sets lborel"
    using measurable_sets[of "\<lambda>x. (r-w)+x" lborel borel ?V] V by (simp add: space_lborel)
  have disj: "?S\<inter>?T={}" by (auto; linarith)
  have split: "{0..<w}\<inter>(\<lambda>x. wrap w (x+r)) -` A = ?S\<union>?T"
  proof (rule set_eqI)
    fix x
    show "x\<in>{0..<w}\<inter>(\<lambda>x. wrap w (x+r)) -` A \<longleftrightarrow> x\<in>?S\<union>?T"
    proof (cases "0\<le>x \<and> x<w")
      case False then show ?thesis using w r by (auto; linarith)
    next
      case True
      show ?thesis
      proof (cases "x+r<w")
        case True
        have eq: "wrap w (x+r)=x+r" by (rule wrap_identity[OF w]) (use True \<open>0\<le>x \<and> x<w\<close> r in linarith)+
        show ?thesis using True \<open>0\<le>x \<and> x<w\<close> r
          by (simp only: Int_iff Un_iff atLeastLessThan_iff vimage_eq eq; smt (verit))
      next
        case False
        have eq: "wrap w (x+r)=x+r-w" by (rule wrap_one_lap[OF w]) (use False \<open>0\<le>x \<and> x<w\<close> r in linarith)+
        show ?thesis using False \<open>0\<le>x \<and> x<w\<close> r
          by (simp only: Int_iff Un_iff atLeastLessThan_iff vimage_eq eq; smt (verit))
      qed
    qed
  qed
  have union: "?U\<union>?V={0..<w}\<inter>A" using r by (auto; linarith)
  have uv: "?U\<inter>?V={}" by auto
  have st: "?T-?S=?T" using disj by blast
  have vu: "?V-?U=?V" using uv by blast
  have "emeasure lborel (?S\<union>?T)=emeasure lborel ?U+emeasure lborel ?V"
    by (simp only: emeasure_Un[OF S T] st translation_emeasure[OF U] translation_emeasure[OF V])
  also have "...=emeasure lborel (?U\<union>?V)"
    using emeasure_Un[of ?U lborel ?V] U V by (simp add: vu)
  finally show ?thesis by (simp only: split union)
qed

theorem circle_motion_preserves_uniform:
  assumes w: "0<w"
  shows "distr (uniform_measure lborel {0..<w}) borel (circle_motion w v u)
    = uniform_measure lborel {0..<w}"
proof (rule measure_eqI)
  show "sets (distr (uniform_measure lborel {0..<w}) borel (circle_motion w v u))
    =sets (uniform_measure lborel {0..<w})" by simp
  fix A assume A: "A\<in>sets (distr (uniform_measure lborel {0..<w}) borel (circle_motion w v u))"
  then have Am[measurable]: "A\<in>sets borel" by simp
  have meas[measurable]: "circle_motion w v u\<in>borel_measurable borel"
    unfolding circle_motion_def by measurable
  have nz: "w\<noteq>0" using w by simp
  have pre[measurable]: "circle_motion w v u -` A\<in>sets lborel"
    using measurable_sets[OF meas Am] by (simp add: space_borel)
  have image: "(\<lambda>x. wrap w (x+v * u))=(\<lambda>x. wrap w (x+wrap w (v * u)))"
    using wrap_shift[OF nz] by blast
  have eq: "emeasure lborel ({0..<w}\<inter>(circle_motion w v u) -` A)
    =emeasure lborel ({0..<w}\<inter>A)"
    unfolding circle_motion_def[abs_def] image
    by (rule wrap_translation_emeasure[OF w wrap_range[OF w] Am])
  show "emeasure (distr (uniform_measure lborel {0..<w}) borel (circle_motion w v u)) A
    =emeasure (uniform_measure lborel {0..<w}) A"
    by (simp add: emeasure_distr emeasure_uniform_measure[OF _ pre] eq)
qed

theorem fiberwise_preserves_product:
  fixes M :: "'a measure" and N :: "'b measure" and F :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes N: "sigma_finite_measure N"
    and joint: "(\<lambda>(p,x). (p,F p x))\<in>measurable (M\<Otimes>\<^sub>M N) (M\<Otimes>\<^sub>M N)"
    and fm: "\<And>p. p\<in>space M \<Longrightarrow> F p\<in>measurable N N"
    and invariant: "\<And>p. p\<in>space M \<Longrightarrow> distr N N (F p)=N"
  shows "distr (M\<Otimes>\<^sub>M N) (M\<Otimes>\<^sub>M N) (\<lambda>(p,x). (p,F p x))=M\<Otimes>\<^sub>M N"
proof (rule measure_eqI)
  interpret N: sigma_finite_measure N by (rule N)
  let ?T = "\<lambda>(p,x). (p,F p x)"
  show "sets(distr (M\<Otimes>\<^sub>M N) (M\<Otimes>\<^sub>M N) ?T)=sets(M\<Otimes>\<^sub>M N)" by simp
  fix A assume A: "A\<in>sets(distr (M\<Otimes>\<^sub>M N) (M\<Otimes>\<^sub>M N) ?T)"
  then have Am: "A\<in>sets(M\<Otimes>\<^sub>M N)" by simp
  let ?B = "?T -` A\<inter>space(M\<Otimes>\<^sub>M N)"
  have Bm: "?B\<in>sets(M\<Otimes>\<^sub>M N)" by (rule measurable_sets[OF joint Am])
  have slices: "\<And>p. p\<in>space M \<Longrightarrow> emeasure N (Pair p -` ?B)=emeasure N (Pair p -` A)"
  proof -
    fix p assume p: "p\<in>space M"
    have sm: "Pair p -` A\<in>sets N" by (rule sets_Pair1[OF Am])
    have eq: "Pair p -` ?B = F p -` (Pair p -` A)\<inter>space N"
      using p by (auto simp: space_pair_measure)
    show "emeasure N (Pair p -` ?B)=emeasure N (Pair p -` A)"
      using emeasure_distr[OF fm[OF p] sm] invariant[OF p] by (simp only: eq)
  qed
  show "emeasure (distr (M\<Otimes>\<^sub>M N) (M\<Otimes>\<^sub>M N) ?T) A=emeasure (M\<Otimes>\<^sub>M N) A"
    by (simp only: emeasure_distr[OF joint Am] N.emeasure_pair_measure_alt[OF Bm]
      N.emeasure_pair_measure_alt[OF Am]) (rule nn_integral_cong, rule slices)
qed

theorem circle_skew_motion_preserves_product:
  assumes w: "0<w" and v[measurable]: "v\<in>borel_measurable M"
  shows "distr (M\<Otimes>\<^sub>M uniform_measure lborel {0..<w})
    (M\<Otimes>\<^sub>M uniform_measure lborel {0..<w})
    (\<lambda>(p,x). (p,circle_motion w (v p) u x))
    =M\<Otimes>\<^sub>M uniform_measure lborel {0..<w}"
proof -
  let ?N = "uniform_measure lborel {0..<w}"
  interpret U: prob_space ?N
    by (rule prob_space_uniform_measure) (use w in auto)
  have joint: "(\<lambda>(p,x). (p,circle_motion w (v p) u x))\<in>measurable (M\<Otimes>\<^sub>M ?N) (M\<Otimes>\<^sub>M ?N)"
    unfolding circle_motion_def wrap_def frac_def by measurable
  have fm: "\<And>p. circle_motion w (v p) u\<in>measurable ?N ?N"
    unfolding circle_motion_def wrap_def frac_def by measurable
  have inv: "\<And>p. distr ?N ?N (circle_motion w (v p) u)=?N"
  proof -
    fix p
    have "distr ?N ?N (circle_motion w (v p) u)=distr ?N borel (circle_motion w (v p) u)"
      by (rule distr_cong) simp_all
    also have "...=?N" by (rule circle_motion_preserves_uniform[OF w])
    finally show "distr ?N ?N (circle_motion w (v p) u)=?N" .
  qed
  show ?thesis by (rule fiberwise_preserves_product[OF U.sigma_finite_measure_axioms joint])
    (rule fm, rule inv)
qed

end
