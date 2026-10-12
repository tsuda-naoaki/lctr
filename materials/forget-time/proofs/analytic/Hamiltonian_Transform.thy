theory Hamiltonian_Transform
  imports Gaussian_Strip "HOL-Analysis.Interval_Integral"
begin

definition gaussian_coordinate :: "real \<Rightarrow> real" where
  "gaussian_coordinate q = (LBINT x=0..q. gaussian x)"

definition thermal_hamiltonian :: "real \<Rightarrow> real \<Rightarrow> real" where
  "thermal_hamiltonian q p = exp(2*q\<^sup>2)*p\<^sup>2 + ln pi"

lemma thermal_generator:
  "-ln(thermal_density q p) = thermal_hamiltonian q p"
  by (simp add: thermal_density_def thermal_hamiltonian_def ln_div)

lemma hamiltonian_q_derivative:
  "DERIV (\<lambda>q. thermal_hamiltonian q p) q :> (4*q*exp(2*q\<^sup>2)*p\<^sup>2)"
  unfolding thermal_hamiltonian_def
  by (auto intro!: derivative_eq_intros simp: algebra_simps)

lemma hamiltonian_p_derivative:
  "DERIV (thermal_hamiltonian q) p :> (2*exp(2*q\<^sup>2)*p)"
  unfolding thermal_hamiltonian_def
  by (auto intro!: derivative_eq_intros simp: algebra_simps)

lemma gaussian_coordinate_derivative:
  "DERIV gaussian_coordinate q :> gaussian q"
proof -
  let ?a = "min 0 q-1"
  let ?b = "max 0 q+1"
  have a0: "?a\<le>0" and b0: "0\<le>?b" and aq: "?a\<le>q" and bq: "q\<le>?b"
    by linarith+
  have cont: "continuous_on {?a..?b} gaussian"
    unfolding gaussian_def by (intro continuous_intros)
  have d: "((\<lambda>u. LBINT y=0..u. gaussian y) has_vector_derivative gaussian q)
    (at q within {?a..?b})"
    using interval_integral_FTC2[OF a0 b0 cont aq bq] by (simp only: zero_ereal_def)
  have bounds: "?a<q" "q<?b" by linarith+
  have linear: "(\<lambda>x. x*gaussian q) = (*) (gaussian q)"
    by (rule ext) (simp add: mult.commute)
  show ?thesis using d bounds
    by (simp add: gaussian_coordinate_def[abs_def] at_within_Icc_at has_vector_derivative_def has_field_derivative_def linear)
qed

theorem transformed_solution_derivatives:
  fixes q p :: "real \<Rightarrow> real"
  assumes qd: "DERIV q u :> (2*exp(2*(q u)\<^sup>2)*p u)"
    and pd: "DERIV p u :> (-4*q u*exp(2*(q u)\<^sup>2)*(p u)\<^sup>2)"
  shows "DERIV (\<lambda>t. gaussian_coordinate (q t)) u :> (2*(exp((q u)\<^sup>2)*p u))"
    and "DERIV (\<lambda>t. exp((q t)\<^sup>2)*p t) u :> 0"
proof -
  have e: "exp(2*(q u)\<^sup>2) = exp((q u)\<^sup>2)^2" by (simp only: exp_double)
  show "DERIV (\<lambda>t. gaussian_coordinate (q t)) u :> (2*(exp((q u)\<^sup>2)*p u))"
    using DERIV_chain2[OF gaussian_coordinate_derivative[of "q u"] qd]
    by (simp only: gaussian_def e exp_minus)
      (simp add: power2_eq_square field_simps)
  show "DERIV (\<lambda>t. exp((q t)\<^sup>2)*p t) u :> 0"
    apply (rule derivative_eq_intros qd pd | simp)+
    by (simp add: e power2_eq_square algebra_simps)
qed

theorem linearised_solution:
  fixes q p :: "real \<Rightarrow> real"
  assumes I: "open I" "connected I" "0\<in>I"
    and qd: "\<And>u. u\<in>I \<Longrightarrow> DERIV q u :> (2*exp(2*(q u)\<^sup>2)*p u)"
    and pd: "\<And>u. u\<in>I \<Longrightarrow> DERIV p u :> (-4*q u*exp(2*(q u)\<^sup>2)*(p u)\<^sup>2)"
    and u: "u\<in>I"
  shows "exp((q u)\<^sup>2)*p u = exp((q 0)\<^sup>2)*p 0"
    and "gaussian_coordinate(q u)=gaussian_coordinate(q 0)+2*(exp((q 0)\<^sup>2)*p 0)*u"
proof -
  let ?P = "\<lambda>t. exp((q t)\<^sup>2)*p t"
  have zerof: "((*) (0::real)) = (\<lambda>x.0)" by (rule ext) simp
  have dP: "\<And>t. t\<in>I \<Longrightarrow> DERIV ?P t :> 0"
    by (rule transformed_solution_derivatives(2)[OF qd pd])
  have Pc: "\<And>t. t\<in>I \<Longrightarrow> ?P t=?P 0"
  proof -
    fix t assume t: "t\<in>I"
    show "?P t=?P 0"
      by (rule has_derivative_zero_unique_connected[OF I(1,2) _ t I(3)])
        (use dP in \<open>simp only: has_field_derivative_def zerof\<close>)
  qed
  show "?P u=?P 0" by (rule Pc[OF u])
  let ?F = "\<lambda>t. gaussian_coordinate(q t)-2*(?P 0)*t"
  have dF: "\<And>t. t\<in>I \<Longrightarrow> DERIV ?F t :> 0"
  proof -
    fix t assume t: "t\<in>I"
    have dQ: "DERIV (\<lambda>t. gaussian_coordinate(q t)) t :> 2*(?P 0)"
      using transformed_solution_derivatives(1)[OF qd[OF t] pd[OF t]] Pc[OF t] by simp
    show "DERIV ?F t :> 0"
      using dQ by (auto intro!: derivative_eq_intros)
  qed
  have "?F u=?F 0"
    by (rule has_derivative_zero_unique_connected[OF I(1,2) _ u I(3)])
      (use dF in \<open>simp only: has_field_derivative_def zerof\<close>)
  then show "gaussian_coordinate(q u)=gaussian_coordinate(q 0)+2*(?P 0)*u" by simp
qed

lemma gaussian_set_integral_bound:
  assumes S: "S\<in>sets lborel"
  shows "abs (\<integral>x\<in>S. gaussian x \<partial>lborel) \<le> sqrt pi"
proof -
  have fi: "integrable lborel (\<lambda>x. indicator S x *\<^sub>R gaussian x)"
    using integrable_mult_indicator[OF S gaussian_integrable]
    by (simp add: mult.commute)
  have point: "\<And>x. norm(indicator S x *\<^sub>R gaussian x)\<le>gaussian x"
    by (simp add: indicator_def gaussian_def)
  have "norm (\<integral>x. indicator S x *\<^sub>R gaussian x \<partial>lborel)
    \<le> (\<integral>x. gaussian x \<partial>lborel)"
    by (rule Bochner_Integration.integral_norm_bound_integral[OF fi gaussian_integrable]) (rule point)
  then show ?thesis
    by (simp add: set_lebesgue_integral_def has_bochner_integral_integral_eq[OF gaussian_integral])
qed

lemma gaussian_coordinate_bound:
  "abs (gaussian_coordinate q) \<le> sqrt pi"
  unfolding gaussian_coordinate_def interval_lebesgue_integral_def
  using gaussian_set_integral_bound[of "einterval 0 (ereal q)"]
    gaussian_set_integral_bound[of "einterval (ereal q) 0"]
  by (auto simp: einterval_def)

theorem nonzero_momentum_no_global_solution:
  fixes q p :: "real \<Rightarrow> real"
  assumes qd: "\<And>u. DERIV q u :> (2*exp(2*(q u)\<^sup>2)*p u)"
    and pd: "\<And>u. DERIV p u :> (-4*q u*exp(2*(q u)\<^sup>2)*(p u)\<^sup>2)"
    and nonzero: "p 0\<noteq>0"
  shows False
proof -
  let ?P = "exp((q 0)\<^sup>2)*p 0"
  let ?Q = "gaussian_coordinate(q 0)"
  let ?u = "(sqrt pi+1-?Q)/(2*?P)"
  have nz: "?P\<noteq>0" using nonzero by simp
  have flow: "gaussian_coordinate(q ?u)=?Q+2*?P*?u"
    apply (rule linearised_solution(2)[where I=UNIV, OF open_UNIV connected_UNIV])
       apply (rule UNIV_I)
      apply (rule qd)
     apply (rule pd)
    apply (rule UNIV_I)
    done
  have hit: "?Q+2*?P*?u=sqrt pi+1" using nz by simp
  have "gaussian_coordinate(q ?u)\<le>sqrt pi"
    using gaussian_coordinate_bound[of "q ?u"] by linarith
  then show False using flow hit by linarith
qed

theorem rescaled_no_global_solution:
  fixes q p :: "real \<Rightarrow> real" and a :: real
  assumes a: "a\<noteq>0"
    and qd: "\<And>u. DERIV q u :> (a*(2*exp(2*(q u)\<^sup>2)*p u))"
    and pd: "\<And>u. DERIV p u :> (a*(-4*q u*exp(2*(q u)\<^sup>2)*(p u)\<^sup>2))"
    and nonzero: "p 0\<noteq>0"
  shows False
proof -
  let ?q = "\<lambda>u. q(u/a)"
  let ?p = "\<lambda>u. p(u/a)"
  have linear: "\<And>u. DERIV (\<lambda>u::real. u/a) u :> (1/a)"
    using a by (auto intro!: derivative_eq_intros)
  have qnew: "\<And>u. DERIV ?q u :> (2*exp(2*(?q u)\<^sup>2)*?p u)"
    using DERIV_chain2[OF qd linear] a by (simp add: field_simps)
  have pnew: "\<And>u. DERIV ?p u :> (-4*?q u*exp(2*(?q u)\<^sup>2)*(?p u)\<^sup>2)"
    using DERIV_chain2[OF pd linear] a by (simp add: field_simps)
  show False by (rule nonzero_momentum_no_global_solution[OF qnew pnew]) (use nonzero in simp)
qed

end
