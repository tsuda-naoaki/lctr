theory Linear_Retraction_Derivatives
  imports "LCTR_Zero_Completed_Derivative.Zero_Completed_Derivative"
begin

lemma zderiv_fixed_linear:
  fixes P :: "'a::real_normed_vector \<Rightarrow> 'a"
  assumes P: "bounded_linear P" and fixed: "\<And>t. P (f t)=f t"
  shows "P (zderiv f x)=zderiv f x"
proof (cases "f differentiable (at x)")
  case True
  have d: "(f has_vector_derivative vector_derivative f (at x)) (at x)"
    by (rule vector_derivative_works[THEN iffD1, OF True])
  have e: "(\<lambda>t. P (f t))=f" by (simp add: fun_eq_iff fixed)
  have pd: "(f has_vector_derivative P (vector_derivative f (at x))) (at x)"
    using bounded_linear.has_vector_derivative[OF P d] by (simp only: e)
  have z: "zderiv f x=P (vector_derivative f (at x))" by (rule zderiv_from_derivative[OF pd])
  show ?thesis using z by (simp add: zderiv_def True)
next
  case False
  interpret PL: bounded_linear P by (rule P)
  show ?thesis by (simp add: zderiv_def False PL.zero)
qed

lemma iterated_zderiv_fixed_linear:
  fixes P :: "'a::real_normed_vector \<Rightarrow> 'a"
  assumes P: "bounded_linear P" and fixed: "\<And>t. P (f t)=f t"
  shows "P ((zderiv ^^ n) f x)=(zderiv ^^ n) f x"
proof (induction n arbitrary: x)
  case 0 show ?case by (simp add: fixed)
next
  case (Suc n)
  show ?case unfolding funpow.simps comp_apply
    by (rule zderiv_fixed_linear[OF P Suc.IH])
qed

locale bounded_linear_retraction =
  fixes F :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector" and G :: "'b \<Rightarrow> 'a"
  assumes F_linear: "bounded_linear F" and G_linear: "bounded_linear G"
begin

lemma retraction_differentiability_iff:
  fixes f :: "real \<Rightarrow> 'a"
  assumes rec: "\<And>t. G (F (f t))=f t"
  shows "(F \<circ> f) differentiable (at x) \<longleftrightarrow> f differentiable (at x)"
proof
  assume h: "(F \<circ> f) differentiable (at x)"
  have d: "((\<lambda>t. G ((F \<circ> f) t)) has_vector_derivative
    G (vector_derivative (F \<circ> f) (at x))) (at x)"
    by (rule bounded_linear.has_vector_derivative[OF G_linear vector_derivative_works[THEN iffD1, OF h]])
  have e: "(\<lambda>t. G ((F \<circ> f) t))=f" by (simp add: fun_eq_iff o_def rec)
  show "f differentiable (at x)" using d by (simp only: e) (rule differentiableI_vector)
next
  assume h: "f differentiable (at x)"
  have d: "((\<lambda>t. F (f t)) has_vector_derivative F (vector_derivative f (at x))) (at x)"
    by (rule bounded_linear.has_vector_derivative[OF F_linear vector_derivative_works[THEN iffD1, OF h]])
  show "(F \<circ> f) differentiable (at x)" using differentiableI_vector[OF d] by (simp add: o_def)
qed

lemma zderiv_retraction_comp:
  assumes rec: "\<And>t. G (F (f t))=f t"
  shows "zderiv (F \<circ> f) x=F (zderiv f x)"
proof (cases "f differentiable (at x)")
  case True
  have d: "((\<lambda>t. F (f t)) has_vector_derivative F (vector_derivative f (at x))) (at x)"
    by (rule bounded_linear.has_vector_derivative[OF F_linear vector_derivative_works[THEN iffD1, OF True]])
  have z: "zderiv (F \<circ> f) x=F (vector_derivative f (at x))"
    using zderiv_from_derivative[OF d] by (simp add: o_def)
  show ?thesis using z by (simp add: zderiv_def True)
next
  case False
  interpret FL: bounded_linear F by (rule F_linear)
  show ?thesis by (simp add: zderiv_def retraction_differentiability_iff[OF rec] False FL.zero)
qed

lemma iterated_retraction_identity:
  assumes rec: "\<And>t. G (F (f t))=f t"
  shows "G (F ((zderiv ^^ n) f x))=(zderiv ^^ n) f x"
proof -
  have P: "bounded_linear (G \<circ> F)"
    using bounded_linear_compose[OF G_linear F_linear] by (simp only: o_def)
  have idf: "\<And>t. (G \<circ> F) (f t)=f t" by (simp add: rec)
  show ?thesis using iterated_zderiv_fixed_linear[OF P idf, where n=n and x=x] by simp
qed

lemma iterated_zderiv_retraction_comp:
  assumes rec: "\<And>t. G (F (f t))=f t"
  shows "(zderiv ^^ n) (F \<circ> f) x=F ((zderiv ^^ n) f x)"
proof (induction n arbitrary: x)
  case 0 show ?case by simp
next
  case (Suc n)
  have e: "(zderiv ^^ n) (F \<circ> f)=F \<circ> ((zderiv ^^ n) f)"
    by (rule ext) (simp only: comp_apply; rule Suc.IH)
  have step: "zderiv ((zderiv ^^ n) (F \<circ> f)) x=F (zderiv ((zderiv ^^ n) f) x)"
    by (subst e) (rule zderiv_retraction_comp[OF iterated_retraction_identity[OF rec]])
  show ?case using step by (simp only: funpow.simps o_def)
qed

end

ML \<open>
val roots = @{thms zderiv_fixed_linear iterated_zderiv_fixed_linear
 bounded_linear_retraction.retraction_differentiability_iff bounded_linear_retraction.zderiv_retraction_comp
 bounded_linear_retraction.iterated_retraction_identity bounded_linear_retraction.iterated_zderiv_retraction_comp};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
