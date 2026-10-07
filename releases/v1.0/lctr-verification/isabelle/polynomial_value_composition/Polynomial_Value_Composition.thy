theory Polynomial_Value_Composition
  imports "LCTR_Value_Jet_Lift_Algebra.Value_Jet_Lift_Algebra"
begin

lemma scalar_jet_factor_smooth:
  "higher_differentiable_on S (\<lambda>x. poly (pderiv (basis_poly i)) (x-a)) n"
proof -
  have eq: "(\<lambda>x. poly (pderiv (basis_poly i)) (x-a)) =
    derivative_family 1 i a (\<lambda>j. if j=i then (1::real) else 0)"
  proof (rule ext)
    fix x
    have factor: "poly (pderiv (basis_poly j)) (x-a) *\<^sub>R
        (if j=i then (1::real) else 0) =
        (if j=i then poly (pderiv (basis_poly i)) (x-a) else 0)" for j
      by (cases "j=i") auto
    have sum: "(\<Sum>j\<le>i. poly (pderiv (basis_poly j)) (x-a) *\<^sub>R
      (if j=i then (1::real) else 0)) = poly (pderiv (basis_poly i)) (x-a)"
    proof -
      have "(\<Sum>j\<le>i. poly (pderiv (basis_poly j)) (x-a) *\<^sub>R
        (if j=i then (1::real) else 0)) =
        (\<Sum>j\<le>i. if j=i then poly (pderiv (basis_poly i)) (x-a) else 0)"
        by (rule sum.cong) (auto simp only: factor)
      also have "... = poly (pderiv (basis_poly i)) (x-a)" by simp
      finally show ?thesis .
    qed
    show "poly (pderiv (basis_poly i)) (x-a) =
      derivative_family 1 i a (\<lambda>j. if j=i then (1::real) else 0) x"
      using sum by (simp add: derivative_family_def)
  qed
  show ?thesis unfolding eq
    by (rule higher_differentiable_on_subset[OF derivative_family_ck]) simp
qed

lemma polynomial_value_composition:
  fixes f :: "'e::real_normed_vector \<Rightarrow> 'f::real_normed_vector"
  assumes fs: "higher_differentiable_on V f k" and S: "open S"
    and maps: "image (jet_curve n a v) S \<subseteq> V"
  shows "higher_differentiable_on S (f \<circ> jet_curve n a v) k"
  using fs
proof (induction k arbitrary: f)
  case 0
  have cu: "higher_differentiable_on UNIV (jet_curve n a v) 0"
    unfolding jet_curve_def by (rule derivative_family_ck)
  have cs: "continuous_on S (jet_curve n a v)"
    using higher_differentiable_on_subset[OF cu, of S]
    by (simp add: higher_differentiable_on.simps)
  show ?case unfolding higher_differentiable_on.simps o_def
    by (rule continuous_on_compose2[where t=V])
      (use 0 cs maps in \<open>auto simp: higher_differentiable_on.simps\<close>)
next
  case (Suc k)
  let ?c = "jet_curve n a v"
  have cd: "?c differentiable (at x)" for x
    unfolding jet_curve_def by (rule differentiableI_vector[OF derivative_family_has_derivative])
  have fd: "f differentiable (at (?c x))" if x: "x\<in>S" for x
    using Suc.prems maps x by (auto simp: higher_differentiable_on.simps)
  have deriv: "frechet_derivative (f \<circ> ?c) (at x) 1 =
    (\<Sum>i\<le>n. poly (pderiv (basis_poly i)) (x-a) *\<^sub>R
      frechet_derivative f (at (?c x)) (v i))" if x: "x\<in>S" for x
  proof -
    interpret df: linear "frechet_derivative f (at (?c x))"
      by (rule linear_frechet_derivative[OF fd[OF x]])
    have cv: "frechet_derivative ?c (at x) 1 = derivative_family 1 n a v x"
      using frechet_derivative_eq_vector_derivative[OF cd[of x]]
        vector_derivative_at[OF derivative_family_has_derivative[where n=0 and k=n and a=a and v=v and x=x]]
      by (simp add: jet_curve_def)
    show ?thesis
      by (simp only: frechet_derivative_compose[OF cd fd[OF x]] comp_apply cv
        derivative_family_def funpow_0 funpow.simps id_apply)
        (simp add: df.sum df.scaleR)
  qed
  have dk: "higher_differentiable_on S
    (\<lambda>x. frechet_derivative f (at (?c x)) (v i)) k" for i
  proof -
    have h: "higher_differentiable_on V (\<lambda>x. frechet_derivative f (at x) (v i)) k"
      using Suc.prems by (auto simp: higher_differentiable_on.simps)
    show ?thesis using Suc.IH[OF h] by (simp add: o_def)
  qed
  have sumk: "higher_differentiable_on S
    (\<lambda>x. \<Sum>i\<le>n. poly (pderiv (basis_poly i)) (x-a) *\<^sub>R
      frechet_derivative f (at (?c x)) (v i)) k"
    by (rule higher_differentiable_on_sum[OF _ S])
      (rule higher_differentiable_on_scaleR[OF scalar_jet_factor_smooth dk S])
  have full: "higher_differentiable_on S
    (\<lambda>x. frechet_derivative (f \<circ> ?c) (at x) 1) k"
    by (rule higher_differentiable_on_congI[OF S sumk deriv])
  have diff: "(f \<circ> ?c) differentiable (at x)" if "x\<in>S" for x
    by (rule differentiable_chain_at[OF cd fd[OF that]])
  show ?case by (simp only: higher_differentiable_on_real_Suc[OF S])
    (use diff full in blast)
qed

lemma native_polynomial_composition_at:
  assumes V: "open V" and fs: "higher_differentiable_on V f k"
    and cv: "jet_curve n b v a\<in>V"
  shows "curve_ck_at k a (f \<circ> jet_curve n b v)"
proof -
  let ?S = "vimage (jet_curve n b v) V"
  have cs: "continuous_on UNIV (jet_curve n b v)"
    using higher_differentiable_on_imp_continuous_on[OF derivative_family_ck[where n=0 and k=n and a=b and v=v]]
    by (simp add: jet_curve_def)
  have op: "open ?S"
    using continuous_on_open_vimage[OF open_UNIV, of "jet_curve n b v"] cs V by simp
  have ck: "higher_differentiable_on ?S (f \<circ> jet_curve n b v) k"
    by (rule polynomial_value_composition[OF fs op]) auto
  show ?thesis unfolding curve_ck_at_def using op cv ck by blast
qed

ML \<open>
val roots = @{thms scalar_jet_factor_smooth polynomial_value_composition native_polynomial_composition_at};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
