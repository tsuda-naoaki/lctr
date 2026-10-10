theory Linear_Domain_Regularity
  imports "LCTR_Native_Atlas_Carriers.Native_Atlas_Carriers"
begin

lemma higher_precompose_bounded_linear:
  fixes G :: "'e::real_normed_vector \<Rightarrow> 'f::real_normed_vector"
    and f :: "'f \<Rightarrow> 'g::real_normed_vector"
  assumes G: "bounded_linear G" and V: "open V"
    and h: "higher_differentiable_on V f k"
  shows "higher_differentiable_on (vimage G V) (f \<circ> G) k"
proof -
  interpret lin: bounded_linear G by (rule G)
  have continuous: "continuous_on UNIV G" by (rule linear_continuous_on[OF G])
  have op: "open (vimage G V)"
    using continuous_on_open_vimage[OF open_UNIV, of G] continuous V by simp
  show ?thesis using h
  proof (induction k arbitrary: f)
    case 0
    show ?case unfolding higher_differentiable_on.simps o_def
      by (rule continuous_on_compose2[where t=V])
        (use 0 linear_continuous_on[OF G] in \<open>auto simp: higher_differentiable_on.simps\<close>)
  next
    case (Suc k)
    have fd: "f differentiable (at x)" if "x\<in>V" for x using Suc.prems that by (auto simp: higher_differentiable_on.simps)
    have gd: "G differentiable (at x)" for x by (rule bounded_linear_imp_differentiable[OF G])
    have der: "frechet_derivative (f \<circ> G) (at x) v =
      frechet_derivative f (at (G x)) (G v)" if "x\<in>vimage G V" for x v
      using frechet_derivative_compose[OF gd fd[of "G x"]] that
      by (simp add: lin.frechet_derivative)
    have ck: "higher_differentiable_on (vimage G V)
      (\<lambda>x. frechet_derivative (f \<circ> G) (at x) v) k" for v
    proof -
      have df: "higher_differentiable_on V (\<lambda>x. frechet_derivative f (at x) (G v)) k"
        using Suc.prems by (auto simp: higher_differentiable_on.simps)
      have rec: "higher_differentiable_on (vimage G V)
        ((\<lambda>x. frechet_derivative f (at x) (G v)) \<circ> G) k"
        by (rule Suc.IH[OF df])
      show ?thesis by (rule higher_differentiable_on_congI[OF op rec]) (simp add: der)
    qed
    have diff: "(f \<circ> G) differentiable (at x)" if "x\<in>vimage G V" for x
      using gd fd that by (auto intro!: differentiable_chain_at)
    show ?case using ck diff by (auto simp: higher_differentiable_on.simps o_def)
  qed
qed

lemma higher_postcompose_bounded_linear:
  fixes F :: "'f::real_normed_vector \<Rightarrow> 'g::real_normed_vector"
    and f :: "'e::real_normed_vector \<Rightarrow> 'f"
  assumes F: "bounded_linear F" and V: "open V"
    and h: "higher_differentiable_on V f k"
  shows "higher_differentiable_on V (F \<circ> f) k"
proof -
  interpret lin: bounded_linear F by (rule F)
  show ?thesis using h
  proof (induction k arbitrary: f)
    case 0
    show ?case unfolding higher_differentiable_on.simps o_def
      by (rule continuous_on_compose2[where t=UNIV])
        (use 0 linear_continuous_on[OF F] in \<open>auto simp: higher_differentiable_on.simps\<close>)
  next
    case (Suc k)
    have fd: "f differentiable (at x)" if "x\<in>V" for x using Suc.prems that by (auto simp: higher_differentiable_on.simps)
    have gd: "F differentiable (at x)" for x by (rule bounded_linear_imp_differentiable[OF F])
    have der: "frechet_derivative (F \<circ> f) (at x) v =
      F (frechet_derivative f (at x) v)" if "x\<in>V" for x v
      using frechet_derivative_compose[OF fd[OF that] gd]
      by (simp add: lin.frechet_derivative)
    have ck: "higher_differentiable_on V
      (\<lambda>x. frechet_derivative (F \<circ> f) (at x) v) k" for v
    proof -
      have df: "higher_differentiable_on V (\<lambda>x. frechet_derivative f (at x) v) k"
        using Suc.prems by (auto simp: higher_differentiable_on.simps)
      have rec: "higher_differentiable_on V
        (F \<circ> (\<lambda>x. frechet_derivative f (at x) v)) k"
        by (rule Suc.IH[OF df])
      show ?thesis by (rule higher_differentiable_on_congI[OF V rec]) (simp add: der)
    qed
    have diff: "(F \<circ> f) differentiable (at x)" if "x\<in>V" for x
      using gd fd that by (auto intro!: differentiable_chain_at)
    show ?case using ck diff by (auto simp: higher_differentiable_on.simps o_def)
  qed
qed

lemma linear_euclidean_model_preserves_curves:
  fixes F :: "'e::real_normed_vector \<Rightarrow> 'f::euclidean_space"
    and G :: "'f \<Rightarrow> 'e" and f :: "'e \<Rightarrow> 'g::real_normed_vector"
  assumes F: "bounded_linear F" and G: "bounded_linear G"
    and rec: "\<And>x. G (F x) = x"
    and V: "open V" and fs: "higher_differentiable_on V f k"
  shows "preserves_ck_curves k a V f"
proof -
  have continuous: "continuous_on UNIV G" by (rule linear_continuous_on[OF G])
  have op: "open (vimage G V)"
    using continuous_on_open_vimage[OF open_UNIV, of G] continuous V by simp
  have smooth: "higher_differentiable_on (vimage G V) (f \<circ> G) k"
    by (rule higher_precompose_bounded_linear[OF G V fs])
  have model: "preserves_ck_curves k a (vimage G V) (f \<circ> G)"
    by (rule euclidean_value_map_preserves_curves[OF op smooth])
  show ?thesis unfolding preserves_ck_curves_def
  proof (intro allI impI)
    fix c assume cs: "curve_ck_at k a c" and at: "c a\<in>V"
    obtain S where S: "open S" "a\<in>S" "higher_differentiable_on S c k"
      using cs unfolding curve_ck_at_def by blast
    have Fcs: "higher_differentiable_on S (F \<circ> c) k"
      by (rule higher_postcompose_bounded_linear[OF F S(1,3)])
    have cks: "curve_ck_at k a (F \<circ> c)"
      unfolding curve_ck_at_def using S(1,2) Fcs by blast
    have inside: "(F \<circ> c) a\<in>vimage G V" using rec at by simp
    have "curve_ck_at k a ((f \<circ> G) \<circ> (F \<circ> c))"
      using model cks inside unfolding preserves_ck_curves_def by blast
    then show "curve_ck_at k a (f \<circ> c)" by (simp add: o_def rec)
  qed
qed

ML \<open>
val roots = @{thms higher_precompose_bounded_linear higher_postcompose_bounded_linear
  linear_euclidean_model_preserves_curves};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
