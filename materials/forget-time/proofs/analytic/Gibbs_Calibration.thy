theory Gibbs_Calibration
  imports "HOL-Analysis.Analysis"
begin

theorem constant_calibration_gibbs:
  fixes H rho :: "'a::real_normed_vector \<Rightarrow> real"
    and DH DR :: "'a \<Rightarrow> 'a \<Rightarrow> real" and k :: real
  assumes V: "open V" "connected V" "V\<noteq>{}"
    and k: "0<k"
    and pos: "\<And>x. x\<in>V \<Longrightarrow> 0<rho x"
    and H: "\<And>x. x\<in>V \<Longrightarrow> (H has_derivative DH x) (at x)"
    and R: "\<And>x. x\<in>V \<Longrightarrow> ((\<lambda>y. -ln(rho y)) has_derivative DR x) (at x)"
    and calibrated: "\<And>x h. x\<in>V \<Longrightarrow> DH x h=k*DR x h"
  shows "\<exists>Z>0. \<forall>x\<in>V. rho x=Z*exp(-H x/k)"
proof -
  obtain a where a: "a\<in>V" using V(3) by blast
  let ?J = "\<lambda>x. H x - k*(-ln(rho x))"
  have zero: "\<And>x. x\<in>V \<Longrightarrow> (?J has_derivative (\<lambda>h.0)) (at x)"
  proof -
    fix x assume x: "x\<in>V"
    have d: "(?J has_derivative (\<lambda>h. DH x h - k*DR x h)) (at x)"
      by (intro derivative_intros H[OF x] R[OF x])
    show "(?J has_derivative (\<lambda>h.0)) (at x)"
      using d calibrated[OF x] by simp
  qed
  have same: "\<And>x. x\<in>V \<Longrightarrow> ?J x=?J a"
    by (rule has_derivative_zero_unique_connected[OF V(1,2) zero _ a])
  let ?Z = "exp (?J a/k)"
  have Z: "0<?Z" by simp
  have shape: "\<And>x. x\<in>V \<Longrightarrow> rho x=?Z*exp(-H x/k)"
  proof -
    fix x assume x: "x\<in>V"
    have num: "k*ln(rho x)=?J a-H x"
      using same[OF x] by linarith
    have quot: "ln(rho x)=(?J a-H x)/k"
      using num k by (simp add: eq_divide_eq mult.commute)
    have log: "ln(rho x) = ?J a/k - H x/k"
      using quot by (simp add: diff_divide_distrib)
    have "rho x = exp (ln(rho x))" using pos[OF x] by simp
    also have "... = ?Z*exp(-H x/k)"
      by (simp add: log exp_diff exp_minus divide_inverse)
    finally show "rho x=?Z*exp(-H x/k)" .
  qed
  show ?thesis using Z shape by blast
qed

theorem gibbs_constant_calibration:
  fixes H rho :: "'a::real_normed_vector \<Rightarrow> real"
    and DH DR :: "'a \<Rightarrow> 'a \<Rightarrow> real" and k Z :: real
  assumes V: "open V" and k: "0<k" and Z: "0<Z"
    and H: "\<And>x. x\<in>V \<Longrightarrow> (H has_derivative DH x) (at x)"
    and R: "\<And>x. x\<in>V \<Longrightarrow> ((\<lambda>y. -ln(rho y)) has_derivative DR x) (at x)"
    and shape: "\<And>x. x\<in>V \<Longrightarrow> rho x=Z*exp(-H x/k)"
    and x: "x\<in>V"
  shows "DH x h=k*DR x h"
proof -
  have eq: "\<And>y. y\<in>V \<Longrightarrow> -ln(rho y)=H y/k-ln Z"
    using Z by (simp add: shape ln_mult)
  have d: "((\<lambda>y. H y/k-ln Z) has_derivative (\<lambda>h. DH x h/k)) (at x)"
    unfolding divide_inverse
    by (auto intro!: derivative_eq_intros H[OF x])
  have dR: "((\<lambda>y. -ln(rho y)) has_derivative (\<lambda>h. DH x h/k)) (at x)"
    by (rule has_derivative_transform_within_open[OF d V x]) (simp add: eq)
  have "DR x=(\<lambda>h. DH x h/k)" by (rule has_derivative_unique[OF R[OF x] dR])
  then show ?thesis using k by simp
qed

theorem gibbs_calibration_iff:
  fixes H rho :: "'a::real_normed_vector \<Rightarrow> real"
    and DH DR :: "'a \<Rightarrow> 'a \<Rightarrow> real" and k :: real
  assumes V: "open V" "connected V" "V\<noteq>{}" and k: "0<k"
    and pos: "\<And>x. x\<in>V \<Longrightarrow> 0<rho x"
    and H: "\<And>x. x\<in>V \<Longrightarrow> (H has_derivative DH x) (at x)"
    and R: "\<And>x. x\<in>V \<Longrightarrow> ((\<lambda>y. -ln(rho y)) has_derivative DR x) (at x)"
  shows "(\<forall>x\<in>V. \<forall>h. DH x h=k*DR x h) \<longleftrightarrow>
    (\<exists>Z>0. \<forall>x\<in>V. rho x=Z*exp(-H x/k))"
  using constant_calibration_gibbs[OF V k pos H R]
    gibbs_constant_calibration[OF V(1) k _ H R] by blast

end
