theory Zero_Completed_Derivative
  imports "LCTR_Core_Finite_Jets_Vector.Core_Finite_Jets_Vector"
begin

definition zderiv :: "(real \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> real \<Rightarrow> 'a" where
  "zderiv f x = (if f differentiable (at x) then vector_derivative f (at x) else 0)"

lemma native_derivative_outside_domain:
  assumes "\<not> f differentiable (at x)"
  shows "vector_derivative f (at x) = (SOME v. False)"
proof -
  have "\<not> (f has_vector_derivative v) (at x)" for v
    using assms differentiableI_vector by blast
  then show ?thesis by (simp add: vector_derivative_def)
qed

lemma zderiv_off_domain:
  "\<not> f differentiable (at x) \<Longrightarrow> zderiv f x = 0"
  by (simp add: zderiv_def)

lemma zderiv_on_domain:
  "f differentiable (at x) \<Longrightarrow> zderiv f x = vderiv f x"
  by (simp add: zderiv_def vderiv_def)

lemma zderiv_from_derivative:
  "(f has_vector_derivative v) (at x) \<Longrightarrow> zderiv f x = v"
  by (simp add: zderiv_def differentiableI_vector vector_derivative_at)

lemma zderiv_smooth_iterate:
  assumes "curve_smooth f"
  shows "(zderiv ^^ n) f = (vderiv ^^ n) f"
proof (induction n)
  case 0 show ?case by simp
next
  case (Suc n)
  have d: "((vderiv ^^ n) f) differentiable (at x)" for x
    using assms unfolding curve_smooth_def
    by (meson differentiableI_vector)
  have e: "zderiv ((vderiv ^^ n) f) = vderiv ((vderiv ^^ n) f)"
    by (rule ext) (rule zderiv_on_domain[OF d])
  show ?case by (simp only: funpow.simps comp_apply Suc.IH e)
qed

lemma zderiv_polynomial_jet:
  assumes "n \<le> k"
  shows "(zderiv ^^ n) (jet_curve k a v) a = v n"
  by (simp add: zderiv_smooth_iterate[OF curve_smooth_native] curve_derivative assms)

locale bounded_linear_inverse =
  fixes F :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
    and G :: "'b \<Rightarrow> 'a"
  assumes F_linear: "bounded_linear F" and G_linear: "bounded_linear G"
    and GF: "\<And>x. G (F x) = x" and FG: "\<And>y. F (G y) = y"
begin

lemma differentiability_iff:
  fixes f :: "real \<Rightarrow> 'a"
  shows "(F \<circ> f) differentiable (at x) \<longleftrightarrow> f differentiable (at x)"
proof
  assume h: "(F \<circ> f) differentiable (at x)"
  have d: "((\<lambda>t. G ((F \<circ> f) t)) has_vector_derivative
      G (vector_derivative (F \<circ> f) (at x))) (at x)"
    using bounded_linear.has_vector_derivative[OF G_linear
      vector_derivative_works[THEN iffD1, OF h]] .
  have e: "(\<lambda>t. G ((F \<circ> f) t)) = f" by (simp add: fun_eq_iff GF)
  show "f differentiable (at x)" using d by (simp only: e) (rule differentiableI_vector)
next
  assume h: "f differentiable (at x)"
  have d: "((\<lambda>t. F (f t)) has_vector_derivative
      F (vector_derivative f (at x))) (at x)"
    using bounded_linear.has_vector_derivative[OF F_linear
      vector_derivative_works[THEN iffD1, OF h]] .
  show "(F \<circ> f) differentiable (at x)"
    using differentiableI_vector[OF d] by (simp add: o_def)
qed

lemma zderiv_comp:
  "zderiv (F \<circ> f) x = F (zderiv f x)"
proof (cases "f differentiable (at x)")
  case True
  have d: "((\<lambda>t. F (f t)) has_vector_derivative
      F (vector_derivative f (at x))) (at x)"
    using bounded_linear.has_vector_derivative[OF F_linear
      vector_derivative_works[THEN iffD1, OF True]] .
  have e: "vector_derivative (F \<circ> f) (at x) = F (vector_derivative f (at x))"
    using vector_derivative_at[OF d] by (simp add: o_def)
  show ?thesis by (simp add: zderiv_def differentiability_iff True e)
next
  case False
  interpret FL: bounded_linear F by (rule F_linear)
  have z: "F 0 = 0" by (rule FL.zero)
  show ?thesis by (simp add: zderiv_def differentiability_iff False z)
qed

lemma iterated_zderiv_comp:
  "(zderiv ^^ n) (\<lambda>t. F (f t)) x = F ((zderiv ^^ n) f x)"
proof (induction n arbitrary: x)
  case 0 show ?case by simp
next
  case (Suc n)
  have e: "(zderiv ^^ n) (\<lambda>t. F (f t)) = F \<circ> ((zderiv ^^ n) f)"
    by (rule ext) (simp only: comp_apply; rule Suc.IH)
  show ?case
    unfolding funpow.simps comp_apply
    by (subst e) (rule zderiv_comp)
qed

lemma inverse_iterated_zderiv:
  "G ((zderiv ^^ n) (F \<circ> f) x) = (zderiv ^^ n) f x"
  by (simp add: o_def iterated_zderiv_comp GF)

end

ML \<open>
val roots = @{thms native_derivative_outside_domain zderiv_off_domain zderiv_on_domain
  zderiv_from_derivative zderiv_smooth_iterate zderiv_polynomial_jet
  bounded_linear_inverse.differentiability_iff bounded_linear_inverse.zderiv_comp
  bounded_linear_inverse.iterated_zderiv_comp bounded_linear_inverse.inverse_iterated_zderiv};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
