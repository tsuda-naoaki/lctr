theory Gaussian_Inverse_Flow
  imports Gaussian_Coordinate_Range Strip_Flow
begin

definition inverse_gaussian_coordinate :: "real \<Rightarrow> real" where
  "inverse_gaussian_coordinate = inv gaussian_coordinate"

lemma inverse_gaussian_left:
  "inverse_gaussian_coordinate (gaussian_coordinate q)=q"
  unfolding inverse_gaussian_coordinate_def
  by (rule inv_f_f[OF strict_mono_imp_inj_on[OF gaussian_coordinate_strict_mono]])

lemma inverse_gaussian_right:
  assumes "y\<in>{-sqrt pi/2<..<sqrt pi/2}"
  shows "gaussian_coordinate (inverse_gaussian_coordinate y)=y"
  using assms gaussian_coordinate_range
  unfolding inverse_gaussian_coordinate_def by (metis f_inv_into_f)

lemma inverse_gaussian_continuous:
  assumes y: "y\<in>{-sqrt pi/2<..<sqrt pi/2}"
  shows "isCont inverse_gaussian_coordinate y"
proof -
  have "isCont inverse_gaussian_coordinate (gaussian_coordinate(inverse_gaussian_coordinate y))"
    by (rule isCont_inverse_function[where d=1])
      (simp, rule inverse_gaussian_left, rule DERIV_isCont[OF gaussian_coordinate_derivative])
  then show ?thesis by (simp only: inverse_gaussian_right[OF y])
qed

lemma inverse_gaussian_derivative:
  assumes y: "y\<in>{-sqrt pi/2<..<sqrt pi/2}"
  shows "DERIV inverse_gaussian_coordinate y :> exp((inverse_gaussian_coordinate y)\<^sup>2)"
proof -
  have d: "DERIV inverse_gaussian_coordinate y :> inverse(gaussian (inverse_gaussian_coordinate y))"
    by (rule has_field_derivative_inverse_basic[OF gaussian_coordinate_derivative _
      inverse_gaussian_continuous[OF y] open_greaterThanLessThan y inverse_gaussian_right])
      (simp add: gaussian_def)
  show ?thesis using d by (simp add: gaussian_def exp_minus)
qed

definition original_q :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "original_q Q P u=inverse_gaussian_coordinate (Q+2*P*u)"

definition original_p :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "original_p Q P u=P*exp(-(original_q Q P u)\<^sup>2)"

theorem original_flow_solves_hamilton:
  assumes domain: "-sqrt pi/2<Q+2*P*u" "Q+2*P*u<sqrt pi/2"
  shows "DERIV (original_q Q P) u :> (2*exp(2*(original_q Q P u)\<^sup>2) * original_p Q P u)"
    and "DERIV (original_p Q P) u :> (-4 * original_q Q P u*exp(2*(original_q Q P u)\<^sup>2)*(original_p Q P u)\<^sup>2)"
proof -
  let ?q = "original_q Q P"
  have linear: "DERIV (\<lambda>u. Q+2*P*u) u :> (2*P)"
    by (auto intro!: derivative_eq_intros)
  have d: "DERIV ?q u :> (2*P*exp((?q u)\<^sup>2))"
    using DERIV_chain2[OF inverse_gaussian_derivative[of "Q+2*P*u"] linear] domain
    by (simp add: original_q_def[abs_def] mult.commute)
  have e: "exp(2*(?q u)\<^sup>2)=exp((?q u)\<^sup>2)^2" by (simp only: exp_double)
  show "DERIV ?q u :> (2*exp(2*(?q u)\<^sup>2) * original_p Q P u)"
    using d by (simp only: original_p_def e exp_minus) (simp add: power2_eq_square field_simps)
  have dp: "DERIV (original_p Q P) u :> (-4*?q u*P\<^sup>2)"
    unfolding original_p_def
    apply (rule derivative_eq_intros d | simp)+
    by (simp add: exp_minus power2_eq_square field_simps)
  show "DERIV (original_p Q P) u :> (-4*?q u*exp(2*(?q u)\<^sup>2)*(original_p Q P u)\<^sup>2)"
    using dp by (simp only: original_p_def e exp_minus) (simp add: power2_eq_square field_simps)
qed

theorem original_flow_unique:
  assumes I: "open I" "connected I" "0\<in>I"
    and qd: "\<And>u. u\<in>I \<Longrightarrow> DERIV q u :> (2*exp(2*(q u)\<^sup>2)*p u)"
    and pd: "\<And>u. u\<in>I \<Longrightarrow> DERIV p u :> (-4*q u*exp(2*(q u)\<^sup>2)*(p u)\<^sup>2)"
    and u: "u\<in>I"
  shows "q u= original_q (gaussian_coordinate(q 0)) (exp((q 0)\<^sup>2)*p 0) u"
    and "p u= original_p (gaussian_coordinate(q 0)) (exp((q 0)\<^sup>2)*p 0) u"
proof -
  let ?Q = "gaussian_coordinate(q 0)"
  let ?P = "exp((q 0)\<^sup>2)*p 0"
  have qeq: "gaussian_coordinate(q u)=?Q+2*?P*u"
    by (rule linearised_solution(2)[OF I qd pd u])
  have qu: "q u= original_q ?Q ?P u"
    using inverse_gaussian_left[of "q u"] qeq by (simp add: original_q_def)
  show "q u= original_q ?Q ?P u" by (rule qu)
  have peq: "exp((q u)\<^sup>2)*p u=?P" by (rule linearised_solution(1)[OF I qd pd u])
  show "p u= original_p ?Q ?P u"
    unfolding original_p_def
    apply (subst qu[symmetric])
    using peq by (simp add: exp_minus field_simps)
qed

definition original_domain :: "real \<Rightarrow> real \<Rightarrow> real set" where
  "original_domain Q P = {u. -sqrt pi/2 < Q+2*P*u \<and> Q+2*P*u < sqrt pi/2}"

lemma original_domain_interval:
  assumes Q: "-sqrt pi/2<Q" "Q<sqrt pi/2"
  shows "original_domain Q P =
    (if P=0 then UNIV else if 0<P
     then {(-sqrt pi/2-Q)/(2*P)<..<(sqrt pi/2-Q)/(2*P)}
     else {(sqrt pi/2-Q)/(2*P)<..<(-sqrt pi/2-Q)/(2*P)})"
proof (cases "P=0")
  case True then show ?thesis using Q by (auto simp: original_domain_def)
next
  case False
  show ?thesis
  proof (cases "0<P")
    case True
    have p: "P\<noteq>0" "0<2*P" using True by auto
    show ?thesis
      apply (simp only: if_not_P[OF p(1)] if_P[OF True])
      apply (rule set_eqI)
      apply (simp only: original_domain_def mem_Collect_eq greaterThanLessThan_iff
        pos_divide_less_eq[OF p(2)] pos_less_divide_eq[OF p(2)])
      by (auto simp: algebra_simps)
  next
    case False
    with \<open>P\<noteq>0\<close> have "P<0" by linarith
    then have p: "P\<noteq>0" "\<not>0<P" "2*P<0" by auto
    show ?thesis
      apply (simp only: if_not_P[OF p(1)] if_not_P[OF p(2)])
      apply (rule set_eqI)
      apply (simp only: original_domain_def mem_Collect_eq greaterThanLessThan_iff
        neg_divide_less_eq[OF p(3)] neg_less_divide_eq[OF p(3)])
      by (auto simp: algebra_simps)
  qed
qed

lemma original_domain_structure:
  assumes Q: "-sqrt pi/2<Q" "Q<sqrt pi/2"
  shows "open (original_domain Q P)" "connected (original_domain Q P)"
    "0\<in>original_domain Q P"
proof -
  show "open (original_domain Q P)"
    by (simp only: original_domain_interval[OF Q]; simp)
  show "connected (original_domain Q P)"
    by (simp only: original_domain_interval[OF Q]; simp)
  show "0\<in>original_domain Q P" using Q by (simp add: original_domain_def)
qed

lemma original_flow_initial:
  "original_q (gaussian_coordinate q) (exp(q\<^sup>2)*p) 0 = q"
  "original_p (gaussian_coordinate q) (exp(q\<^sup>2)*p) 0 = p"
  by (simp_all add: original_q_def original_p_def inverse_gaussian_left exp_minus)

theorem original_flow_maximal_domain:
  assumes I: "open I" "connected I" "0\<in>I"
    and qd: "\<And>u. u\<in>I \<Longrightarrow> DERIV q u :> (2*exp(2*(q u)\<^sup>2)*p u)"
    and pd: "\<And>u. u\<in>I \<Longrightarrow> DERIV p u :> (-4*q u*exp(2*(q u)\<^sup>2)*(p u)\<^sup>2)"
  shows "I \<subseteq> original_domain (gaussian_coordinate(q 0)) (exp((q 0)\<^sup>2)*p 0)"
proof
  fix u assume "u\<in>I"
  have eq: "gaussian_coordinate(q u)=gaussian_coordinate(q 0)+2*(exp((q 0)\<^sup>2)*p 0)*u"
    by (rule linearised_solution(2)[OF I qd pd \<open>u\<in>I\<close>])
  show "u\<in>original_domain (gaussian_coordinate(q 0)) (exp((q 0)\<^sup>2)*p 0)"
    using gaussian_coordinate_bounds[of "q u"]
    unfolding original_domain_def by (simp only: mem_Collect_eq eq)
qed

end
