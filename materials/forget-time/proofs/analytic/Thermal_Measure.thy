theory Thermal_Measure
  imports Gaussian_Pushforward
begin

lemma thermal_density_scaled:
  "exp(-q\<^sup>2) * thermal_density q (exp(-q\<^sup>2)*p)
    = (gaussian q / sqrt pi) * (gaussian p / sqrt pi)"
proof -
  have e: "exp(2*q\<^sup>2)=(exp(q\<^sup>2))\<^sup>2" by (simp only: exp_double)
  have d: "thermal_density q (exp(-q\<^sup>2)*p)=gaussian p/pi"
    unfolding thermal_density_def gaussian_def
    by (simp only: e exp_minus power_mult_distrib) (simp add: field_simps exp_minus)
  show ?thesis unfolding d gaussian_def
    by (simp add: field_simps mult.assoc[symmetric])
qed

lemma scaled_thermal_integral:
  fixes f :: "real \<Rightarrow> ennreal"
  assumes fm[measurable]: "f\<in>borel_measurable borel"
  shows "(\<integral>\<^sup>+p. ennreal(thermal_density q p)*f(exp(q\<^sup>2)*p) \<partial>lborel)
    = ennreal(gaussian q / sqrt pi) * (\<integral>\<^sup>+p. f p \<partial>gaussian_state)"
proof -
  let ?c = "exp(-q\<^sup>2)"
  let ?g = "\<lambda>p. ennreal(thermal_density q p)*f(exp(q\<^sup>2)*p)"
  have gm[measurable]: "?g\<in>borel_measurable borel"
    unfolding thermal_density_def by measurable
  have sub: "(\<integral>\<^sup>+p. ?g p \<partial>lborel)
    = ennreal ?c * (\<integral>\<^sup>+p. ?g(?c*p) \<partial>lborel)"
    using nn_integral_real_affine[OF gm, of ?c 0] by simp
  have gm2[measurable]: "(\<lambda>p. ?g(?c*p))\<in>borel_measurable lborel" by measurable
  have weight: "ennreal ?c * ennreal(thermal_density q (?c*p))
    = ennreal(gaussian q/sqrt pi)*ennreal(gaussian p/sqrt pi)" for p
  proof -
    have e: "ennreal ?c * ennreal(thermal_density q (?c*p))
      =ennreal(?c*thermal_density q (?c*p))"
      by (rule ennreal_mult[symmetric]) (simp_all add: thermal_density_def)
    show ?thesis by (simp only: e thermal_density_scaled)
      (rule ennreal_mult; simp add: gaussian_def)
  qed
  have point: "ennreal ?c * ?g(?c*p)
    =ennreal(gaussian q/sqrt pi)*(ennreal(gaussian p/sqrt pi)*f p)" for p
  proof -
    have cancel: "exp(q\<^sup>2)*?c=1" by (simp add: exp_minus)
    show ?thesis by (simp only: mult.assoc[symmetric] cancel mult_1_left weight)
  qed
  have dens[measurable]: "(\<lambda>p. ennreal(gaussian p/sqrt pi))\<in>borel_measurable lborel"
    unfolding gaussian_def by measurable
  have "ennreal ?c * (\<integral>\<^sup>+p. ?g(?c*p) \<partial>lborel)
    =(\<integral>\<^sup>+p. ennreal ?c * ?g(?c*p) \<partial>lborel)"
    by (simp add: nn_integral_cmult)
  also have "...=ennreal(gaussian q/sqrt pi)*(\<integral>\<^sup>+p. f p \<partial>gaussian_state)"
    by (simp add: point nn_integral_cmult gaussian_state_def nn_integral_density)
  finally show ?thesis using sub by simp
qed

definition momentum_transform :: "real\<times>real \<Rightarrow> real\<times>real" where
  "momentum_transform s=(fst s,exp((fst s)\<^sup>2) * snd s)"

lemma momentum_transform_measurable[measurable]:
  "momentum_transform\<in>measurable (lborel\<Otimes>\<^sub>M lborel) (lborel\<Otimes>\<^sub>M lborel)"
  unfolding momentum_transform_def by measurable

theorem momentum_transform_integral:
  fixes f :: "real\<times>real \<Rightarrow> ennreal"
  assumes fm[measurable]: "f\<in>borel_measurable (lborel\<Otimes>\<^sub>M lborel)"
  shows "(\<integral>\<^sup>+s. f(momentum_transform s) \<partial>thermal_state)
    =(\<integral>\<^sup>+s. f s \<partial>(gaussian_state\<Otimes>\<^sub>M gaussian_state))"
proof -
  interpret G: prob_space gaussian_state by (rule gaussian_state_probability)
  let ?g = "\<lambda>(q,p). ennreal(thermal_density q p)*f(q,exp(q\<^sup>2)*p)"
  have gm[measurable]: "?g\<in>borel_measurable (lborel\<Otimes>\<^sub>M lborel)"
    unfolding thermal_density_def by measurable
  have slice[measurable]: "(\<lambda>p. f(q,p))\<in>borel_measurable borel" for q
  proof -
    have "(\<lambda>p. f(q,p))\<in>borel_measurable lborel"
      by (rule measurable_compose_Pair1[OF _ fm]) simp
    then show ?thesis by simp
  qed
  have fmG[measurable]: "f\<in>borel_measurable (gaussian_state\<Otimes>\<^sub>M gaussian_state)"
    using fm by (simp add: gaussian_state_def sets_pair_measure)
  have inner[measurable]: "(\<lambda>q. \<integral>\<^sup>+p. f(q,p) \<partial>gaussian_state)\<in>borel_measurable lborel"
    by (rule G.borel_measurable_nn_integral) (use fm in \<open>simp add: gaussian_state_def sets_pair_measure\<close>)
  have dens[measurable]: "(\<lambda>p. ennreal(gaussian p/sqrt pi))\<in>borel_measurable lborel"
    unfolding gaussian_def by measurable
  have td[measurable]: "(\<lambda>(q,p). ennreal(thermal_density q p))\<in>borel_measurable (lborel\<Otimes>\<^sub>M lborel)"
    unfolding thermal_density_def by measurable
  have ft[measurable]: "(\<lambda>s. f(momentum_transform s))\<in>borel_measurable (lborel\<Otimes>\<^sub>M lborel)"
    using measurable_comp[OF momentum_transform_measurable fm] by (simp add: o_def)
  have "(\<integral>\<^sup>+s. f(momentum_transform s) \<partial>thermal_state)
    =(\<integral>\<^sup>+s. ?g s \<partial>(lborel\<Otimes>\<^sub>M lborel))"
    unfolding thermal_state_def
    by (subst nn_integral_density[OF td ft])
      (rule nn_integral_cong; simp add: momentum_transform_def split: prod.splits)
  also have "...=(\<integral>\<^sup>+q. \<integral>\<^sup>+p. ennreal(thermal_density q p)*f(q,exp(q\<^sup>2)*p) \<partial>lborel \<partial>lborel)"
    using lborel.nn_integral_fst[OF gm] by simp
  also have "...=(\<integral>\<^sup>+q. ennreal(gaussian q/sqrt pi)*(\<integral>\<^sup>+p. f(q,p) \<partial>gaussian_state) \<partial>lborel)"
    by (simp only: scaled_thermal_integral[OF slice])
  also have "...=(\<integral>\<^sup>+q. \<integral>\<^sup>+p. f(q,p) \<partial>gaussian_state \<partial>gaussian_state)"
    by (simp add: gaussian_state_def nn_integral_density)
  also have "...=(\<integral>\<^sup>+s. f s \<partial>(gaussian_state\<Otimes>\<^sub>M gaussian_state))"
    by (rule G.nn_integral_fst[OF fmG])
  finally show ?thesis .
qed

theorem momentum_transform_pushforward:
  "distr thermal_state (lborel\<Otimes>\<^sub>M lborel) momentum_transform
    =gaussian_state\<Otimes>\<^sub>M gaussian_state"
proof (rule measure_eqI)
  let ?M = "lborel\<Otimes>\<^sub>M lborel"
  have tm[measurable]: "momentum_transform\<in>measurable thermal_state ?M"
    by (simp add: thermal_state_def)
  show "sets(distr thermal_state ?M momentum_transform)=sets(gaussian_state\<Otimes>\<^sub>M gaussian_state)"
    by (simp add: gaussian_state_def sets_pair_measure)
  fix A assume "A\<in>sets(distr thermal_state ?M momentum_transform)"
  then have Am[measurable]: "A\<in>sets ?M" by simp
  have ind[measurable]: "(indicator A :: real\<times>real\<Rightarrow>ennreal)\<in>borel_measurable ?M"
    by measurable
  have indD: "(indicator A :: real\<times>real\<Rightarrow>ennreal)\<in>borel_measurable (distr thermal_state ?M momentum_transform)"
    by simp
  have Ag: "A\<in>sets(gaussian_state\<Otimes>\<^sub>M gaussian_state)"
    using Am by (simp add: gaussian_state_def sets_pair_measure)
  have Ad: "A\<in>sets(distr thermal_state ?M momentum_transform)" using Am by simp
  show "emeasure(distr thermal_state ?M momentum_transform) A=emeasure(gaussian_state\<Otimes>\<^sub>M gaussian_state) A"
    using momentum_transform_integral[OF ind] nn_integral_distr[OF tm indD]
    by (simp only: nn_integral_indicator[OF Ag] nn_integral_indicator[OF Ad])
qed

definition thermal_coordinates :: "real\<times>real \<Rightarrow> real\<times>real" where
  "thermal_coordinates s=(gaussian_coordinate(fst s),exp((fst s)\<^sup>2) * snd s)"

theorem thermal_coordinates_pushforward:
  "distr thermal_state (lborel\<Otimes>\<^sub>M lborel) thermal_coordinates
    =strip_state (sqrt pi/2)"
proof -
  let ?M = "lborel\<Otimes>\<^sub>M lborel"
  let ?I = "{-sqrt pi/2<..<sqrt pi/2}"
  let ?T = "\<lambda>(q,p). (gaussian_coordinate q,p)"
  interpret G: prob_space gaussian_state by (rule gaussian_state_probability)
  have Fm: "gaussian_coordinate\<in>measurable gaussian_state lborel"
    by (simp add: gaussian_state_def)
  have idm: "(\<lambda>x. x)\<in>measurable gaussian_state lborel"
    by (simp add: gaussian_state_def)
  have id: "distr gaussian_state lborel (\<lambda>x. x)=gaussian_state"
    by (rule distr_id2) (simp add: gaussian_state_def)
  have sf: "sigma_finite_measure(distr gaussian_state lborel (\<lambda>x. x))"
    using G.sigma_finite_measure_axioms by (simp only: id)
  have Fpush: "distr gaussian_state lborel gaussian_coordinate=uniform_measure lborel ?I"
  proof -
    have "distr gaussian_state lborel gaussian_coordinate=distr gaussian_state borel gaussian_coordinate"
      by (rule distr_cong) simp_all
    also have "...=uniform_measure lborel ?I" by (rule gaussian_coordinate_pushforward)
    finally show ?thesis .
  qed
  have qpush: "distr (gaussian_state\<Otimes>\<^sub>M gaussian_state) ?M ?T=strip_state(sqrt pi/2)"
    using pair_measure_distr[OF Fm idm sf]
    by (simp add: id Fpush strip_state_def)
  have mom: "momentum_transform\<in>measurable thermal_state ?M"
    by (simp add: thermal_state_def)
  have qm: "?T\<in>measurable ?M ?M" by measurable
  have comp: "?T \<circ> momentum_transform=thermal_coordinates"
    by (auto simp: fun_eq_iff o_def momentum_transform_def thermal_coordinates_def)
  have "distr thermal_state ?M thermal_coordinates = distr(distr thermal_state ?M momentum_transform) ?M ?T"
    using distr_distr[OF qm mom] by (simp only: comp)
  also have "...=strip_state(sqrt pi/2)"
    by (simp only: momentum_transform_pushforward qpush)
  finally show ?thesis .
qed

theorem original_undefined_positive_probability:
  assumes "u\<noteq>0"
  shows "0<emeasure thermal_state
    {s. u\<notin>original_domain (gaussian_coordinate(fst s)) (exp((fst s)\<^sup>2) * snd s)}"
proof -
  let ?L = "sqrt pi/2"
  let ?M = "lborel\<Otimes>\<^sub>M lborel"
  have tm: "thermal_coordinates\<in>measurable thermal_state ?M"
    unfolding thermal_coordinates_def thermal_state_def by measurable
  have Am: "-strip_domain ?L u\<in>sets ?M"
  proof -
    have "space ?M - strip_domain ?L u\<in>sets ?M"
      by (rule sets.compl_sets) (use strip_domain_measurable[of ?L u] in simp)
    then show ?thesis by (simp add: space_pair_measure Compl_eq_Diff_UNIV)
  qed
  have pre: "thermal_coordinates -` (-strip_domain ?L u) \<inter> space thermal_state
    ={s. u\<notin>original_domain (gaussian_coordinate(fst s)) (exp((fst s)\<^sup>2) * snd s)}"
    using gaussian_coordinate_bounds
    by (auto simp: thermal_state_def space_pair_measure thermal_coordinates_def
      strip_domain_def original_domain_def)
  have eq: "emeasure (strip_state ?L) (-strip_domain ?L u)
    =emeasure thermal_state (thermal_coordinates -` (-strip_domain ?L u) \<inter> space thermal_state)"
    using emeasure_distr[OF tm Am] thermal_coordinates_pushforward by simp
  have miss: "{s. strip_flow ?L u s=None}=-strip_domain ?L u"
    by (auto simp: strip_flow_def)
  show ?thesis using strip_undefined_positive_probability[of ?L u] assms eq
    by (simp only: miss pre) simp
qed

corollary original_flow_not_almost_everywhere:
  assumes "u\<noteq>0"
  shows "\<not>(AE s in thermal_state. u\<in>original_domain
    (gaussian_coordinate(fst s)) (exp((fst s)\<^sup>2) * snd s))"
proof -
  let ?A = "{s. u\<notin>original_domain (gaussian_coordinate(fst s)) (exp((fst s)\<^sup>2) * snd s)}"
  have Am: "?A\<in>sets thermal_state"
    by (rule emeasure_neq_0_sets)
      (use original_undefined_positive_probability[OF assms] in simp)
  have eq: "{s\<in>space thermal_state. u\<notin>original_domain
    (gaussian_coordinate(fst s)) (exp((fst s)\<^sup>2) * snd s)}=?A"
    by (simp add: thermal_state_def space_pair_measure)
  show ?thesis using AE_iff_measurable[OF Am eq]
    original_undefined_positive_probability[OF assms] by auto
qed

corollary rescaled_original_undefined:
  assumes "a\<noteq>0" "u\<noteq>0"
  shows "0<emeasure thermal_state {s. a*u\<notin>original_domain
    (gaussian_coordinate(fst s)) (exp((fst s)\<^sup>2) * snd s)}"
  by (rule original_undefined_positive_probability) (use assms in simp)

end
