theory Gaussian_Pushforward
  imports Gaussian_Inverse_Flow "HOL-Analysis.Lebesgue_Integral_Substitution"
begin

lemma nn_integral_incseq_sets:
  fixes f :: "'a \<Rightarrow> ennreal" and S :: "nat \<Rightarrow> 'a set"
  assumes fm[measurable]: "f\<in>borel_measurable M"
    and Sm[measurable]: "\<And>n. S n\<in>sets M" and inc: "incseq S"
  shows "(\<integral>\<^sup>+x. f x * indicator (\<Union>n. S n) x \<partial>M)
    = (SUP n. \<integral>\<^sup>+x. f x * indicator (S n) x \<partial>M)"
proof -
  have eq: "(SUP n. f x * indicator (S n) x)=f x * indicator (\<Union>n. S n) x" for x
  proof (cases "x\<in>(\<Union>n. S n)")
    case False then show ?thesis by simp
  next
    case True
    then obtain n where n: "x\<in>S n" by blast
    have lo: "f x\<le>(SUP n. f x * indicator (S n) x)"
      using SUP_upper[of n UNIV "\<lambda>n. f x * indicator (S n) x"] n by simp
    have hi: "(SUP n. f x * indicator (S n) x)\<le>f x"
      by (rule SUP_least) (simp split: split_indicator)
    show ?thesis using True lo hi by simp
  qed
  have incf: "incseq (\<lambda>n x. f x * indicator (S n) x)"
    using inc by (auto simp: incseq_def le_fun_def split: split_indicator)
  show ?thesis
    using nn_integral_monotone_convergence_SUP[OF incf] by (simp add: eq)
qed

lemma gaussian_coordinate_measurable[measurable]:
  "gaussian_coordinate\<in>borel_measurable borel"
  by (rule borel_measurable_continuous_onI)
    (intro continuous_at_imp_continuous_on ballI DERIV_isCont[OF gaussian_coordinate_derivative])

theorem gaussian_coordinate_substitution:
  fixes f :: "real \<Rightarrow> ennreal"
  assumes fm[measurable]: "f\<in>borel_measurable borel"
  shows "(\<integral>\<^sup>+y. f y * indicator {-sqrt pi/2<..<sqrt pi/2} y \<partial>lborel)
    = (\<integral>\<^sup>+x. f (gaussian_coordinate x) * ennreal (gaussian x) \<partial>lborel)"
proof -
  let ?a = "\<lambda>n::nat. -(real n+1)"
  let ?b = "\<lambda>n::nat. real n+1"
  let ?S = "\<lambda>n. {?a n..?b n}"
  let ?T = "\<lambda>n. {gaussian_coordinate(?a n)..gaussian_coordinate(?b n)}"
  have incS: "incseq ?S" by (auto simp: incseq_def; linarith)
  have incT: "incseq ?T"
    using monoD[OF strict_mono_mono[OF gaussian_coordinate_strict_mono]]
    by (auto simp: incseq_def; force)
  have unS: "(\<Union>n. ?S n)=UNIV"
  proof (rule set_eqI)
    fix x
    obtain n::nat where "abs x<real n" using reals_Archimedean2 by blast
    then have "x\<in>?S n" using abs_ge_self[of x] abs_ge_minus_self[of x] by (simp; linarith)
    then show "(x\<in>(\<Union>n. ?S n))=(x\<in>UNIV)" by blast
  qed
  have unT: "(\<Union>n. ?T n)={-sqrt pi/2<..<sqrt pi/2}"
  proof (rule set_eqI)
    fix y
    show "y\<in>(\<Union>n. ?T n) \<longleftrightarrow> y\<in>{-sqrt pi/2<..<sqrt pi/2}"
    proof
      assume "y\<in>(\<Union>n. ?T n)"
      then obtain n where "gaussian_coordinate(?a n)\<le>y" "y\<le>gaussian_coordinate(?b n)" by auto
      then show "y\<in>{-sqrt pi/2<..<sqrt pi/2}"
        using gaussian_coordinate_bounds[of "?a n"] gaussian_coordinate_bounds[of "?b n"] by auto
    next
      assume "y\<in>{-sqrt pi/2<..<sqrt pi/2}"
      then obtain x where x: "y=gaussian_coordinate x" using gaussian_coordinate_range by blast
      obtain n where "x\<in>?S n" using unS by blast
      then have "y\<in>?T n" unfolding x
        using monoD[OF strict_mono_mono[OF gaussian_coordinate_strict_mono]] by auto
      then show "y\<in>(\<Union>n. ?T n)" by blast
    qed
  qed
  have finite_sub: "(\<integral>\<^sup>+x. f x * indicator (?T n) x \<partial>lborel)
    = (\<integral>\<^sup>+x. (f (gaussian_coordinate x) * ennreal(gaussian x)) * indicator (?S n) x \<partial>lborel)" for n
    by (rule nn_integral_substitution_aux[OF fm _ gaussian_coordinate_derivative])
      (auto simp: gaussian_def intro!: continuous_intros)
  have rightm[measurable]: "(\<lambda>x. f (gaussian_coordinate x) * ennreal(gaussian x))\<in>borel_measurable lborel"
    unfolding gaussian_def by measurable
  have left: "(\<integral>\<^sup>+x. f x * indicator (\<Union>n. ?T n) x \<partial>lborel)
    = (SUP n. \<integral>\<^sup>+x. f x * indicator (?T n) x \<partial>lborel)"
    by (rule nn_integral_incseq_sets[OF _ _ incT]) (simp_all add: fm)
  have right: "(\<integral>\<^sup>+x. (f (gaussian_coordinate x) * ennreal(gaussian x)) * indicator (\<Union>n. ?S n) x \<partial>lborel)
    = (SUP n. \<integral>\<^sup>+x. (f (gaussian_coordinate x) * ennreal(gaussian x)) * indicator (?S n) x \<partial>lborel)"
    by (rule nn_integral_incseq_sets[OF rightm _ incS]) simp
  show ?thesis using left right by (simp only: unS unT finite_sub indicator_UNIV mult_1_right)
qed

theorem gaussian_coordinate_pushforward:
  "distr gaussian_state borel gaussian_coordinate
    = uniform_measure lborel {-sqrt pi/2<..<sqrt pi/2}"
proof (rule measure_eqI)
  let ?I = "{-sqrt pi/2<..<sqrt pi/2}"
  show "sets (distr gaussian_state borel gaussian_coordinate)=sets (uniform_measure lborel ?I)" by simp
  fix A assume Am: "A\<in>sets (distr gaussian_state borel gaussian_coordinate)"
  then have A[measurable]: "A\<in>sets borel" by simp
  have ind[measurable]: "(indicator A :: real\<Rightarrow>ennreal)\<in>borel_measurable borel"
    by measurable
  have ii: "(indicator A x::ennreal)*indicator ?I x=indicator (?I\<inter>A) x" for x
    by (simp split: split_indicator)
  have ie: "(\<integral>\<^sup>+x. (indicator A x::ennreal)*indicator ?I x \<partial>lborel)=emeasure lborel (?I\<inter>A)"
    by (simp only: ii) (simp add: A)
  have sub: "(\<integral>\<^sup>+x. indicator A (gaussian_coordinate x) * ennreal(gaussian x) \<partial>lborel)
    =emeasure lborel (?I\<inter>A)"
    using gaussian_coordinate_substitution[OF ind] ie by simp
  have dens[measurable]: "(\<lambda>x. ennreal(gaussian x/sqrt pi))\<in>borel_measurable lborel"
    unfolding gaussian_def by measurable
  have comp[measurable]: "(\<lambda>x. indicator A (gaussian_coordinate x)*ennreal(gaussian x))\<in>borel_measurable lborel"
    unfolding gaussian_def by measurable
  have calc: "(\<integral>\<^sup>+x. ennreal(gaussian x/sqrt pi)*indicator A (gaussian_coordinate x) \<partial>lborel)
    =emeasure lborel (?I\<inter>A)/ennreal(sqrt pi)"
  proof -
    have eq: "ennreal(gaussian x/sqrt pi)*indicator A (gaussian_coordinate x)
      = (indicator A (gaussian_coordinate x)*ennreal(gaussian x))/ennreal(sqrt pi)" for x
      by (simp add: divide_ennreal gaussian_def split: split_indicator)
    show ?thesis by (simp only: eq nn_integral_divide[OF comp] sub)
  qed
  have cm[measurable]: "gaussian_coordinate\<in>borel_measurable gaussian_state"
    by (simp add: gaussian_state_def)
  have pre[measurable]: "gaussian_coordinate -` A\<in>sets lborel"
    using measurable_sets[OF gaussian_coordinate_measurable A] by simp
  have indpre: "indicator (gaussian_coordinate -` A) x=indicator A (gaussian_coordinate x)" for x
    by (simp add: indicator_def)
  show "emeasure (distr gaussian_state borel gaussian_coordinate) A
    =emeasure (uniform_measure lborel ?I) A"
    by (simp add: emeasure_distr gaussian_state_def emeasure_density[OF dens pre] calc indpre)
qed

end
