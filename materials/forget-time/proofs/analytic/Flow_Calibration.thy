theory Flow_Calibration
  imports Gibbs_Calibration Observable_Correspondence
begin

theorem observable_curve_calibration:
  fixes phi psi :: "real \<Rightarrow> 'a::real_normed_vector"
    and chi :: "real \<Rightarrow> real"
  assumes sep: "\<And>x y. x\<in>V \<Longrightarrow> y\<in>V \<Longrightarrow>
      (\<forall>f\<in>A. f x=f y) \<Longrightarrow> x=y"
    and I: "open I" "0\<in>I"
    and ranges: "\<And>r. r\<in>I \<Longrightarrow> psi r\<in>V"
      "\<And>r. r\<in>I \<Longrightarrow> phi(chi r)\<in>V"
    and eq: "\<And>r f. r\<in>I \<Longrightarrow> f\<in>A \<Longrightarrow> f(psi r)=f(phi(chi r))"
    and phi: "(phi has_vector_derivative Y) (at 0)"
    and psi: "(psi has_vector_derivative X) (at 0)"
    and chi: "(chi has_vector_derivative k) (at 0)" "chi 0=0"
  shows "X=k *\<^sub>R Y"
proof -
  have curves: "\<And>r. r\<in>I \<Longrightarrow> psi r=phi(chi r)"
    by (rule sep[OF ranges]) (use eq in auto)
  have d: "((\<lambda>r. phi(chi r)) has_vector_derivative (k *\<^sub>R Y)) (at 0)"
    using vector_diff_chain_at[OF chi(1), of phi Y] phi chi(2) by (simp add: o_def)
  have dp: "(psi has_vector_derivative (k *\<^sub>R Y)) (at 0)"
    by (rule has_vector_derivative_transform_within_open[OF d I]) (simp add: curves)
  show ?thesis by (rule vector_derivative_unique_at[OF psi dp])
qed

theorem hamiltonian_field_calibration:
  fixes omega :: "'a::real_vector \<Rightarrow> 'a \<Rightarrow> real"
  assumes linear: "\<And>a x h. omega (a *\<^sub>R x) h=a * omega x h"
    and nondeg: "\<And>x y. (\<And>h. omega x h = omega y h) \<Longrightarrow> x=y"
    and H: "\<And>h. DH h = omega X h"
    and R: "\<And>h. DR h = omega Y h"
  shows "X=k *\<^sub>R Y \<longleftrightarrow> (\<forall>h. DH h=k*DR h)"
proof
  assume eq: "X=k *\<^sub>R Y"
  show "\<forall>h. DH h=k*DR h"
  proof
    fix h
    have "DH h = omega X h" by (rule H)
    also have "...=k * omega Y h" by (simp only: eq linear)
    also have "...=k*DR h" by (simp only: R)
    finally show "DH h=k*DR h" .
  qed
next
  assume eq: "\<forall>h. DH h=k*DR h"
  show "X=k *\<^sub>R Y"
  proof (rule nondeg)
    fix h
    have "omega X h=DH h" by (rule H[symmetric])
    also have "...=k*DR h" using eq by blast
    also have "... = omega (k *\<^sub>R Y) h" by (simp only: R linear)
    finally show "omega X h = omega (k *\<^sub>R Y) h" .
  qed
qed

theorem field_calibration_gibbs_iff:
  fixes H rho :: "'a::real_normed_vector \<Rightarrow> real"
    and omega :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real"
  assumes V: "open V" "connected V" "V\<noteq>{}" and k: "0<k"
    and pos: "\<And>x. x\<in>V \<Longrightarrow> 0<rho x"
    and H: "\<And>x. x\<in>V \<Longrightarrow> (H has_derivative DH x) (at x)"
    and R: "\<And>x. x\<in>V \<Longrightarrow> ((\<lambda>y. -ln(rho y)) has_derivative DR x) (at x)"
    and linear: "\<And>x a v h. x\<in>V \<Longrightarrow> omega x (a *\<^sub>R v) h=a * omega x v h"
    and nondeg: "\<And>x v w. x\<in>V \<Longrightarrow> (\<And>h. omega x v h = omega x w h) \<Longrightarrow> v=w"
    and HX: "\<And>x h. x\<in>V \<Longrightarrow> DH x h = omega x (X x) h"
    and RY: "\<And>x h. x\<in>V \<Longrightarrow> DR x h = omega x (Y x) h"
  shows "(\<forall>x\<in>V. X x=k *\<^sub>R Y x) \<longleftrightarrow>
    (\<exists>Z>0. \<forall>x\<in>V. rho x=Z*exp(-H x/k))"
proof -
  have eq: "X x=k *\<^sub>R Y x \<longleftrightarrow> (\<forall>h. DH x h=k*DR x h)" if "x\<in>V" for x
    by (rule hamiltonian_field_calibration[OF linear[OF that] nondeg[OF that] HX[OF that] RY[OF that]])
  have gibbs: "(\<forall>x\<in>V. \<forall>h. DH x h=k*DR x h) \<longleftrightarrow>
    (\<exists>Z>0. \<forall>x\<in>V. rho x=Z*exp(-H x/k))"
    by (rule gibbs_calibration_iff[OF V k]) (auto intro: pos H R)
  show ?thesis using eq gibbs by blast
qed

end
