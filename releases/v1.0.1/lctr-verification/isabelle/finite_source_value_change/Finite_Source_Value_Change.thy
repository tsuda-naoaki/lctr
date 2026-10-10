theory Finite_Source_Value_Change
  imports "LCTR_Linear_Domain_Regularity.Linear_Domain_Regularity"
begin

lemma zero_order_preserves_curves:
  assumes V: "open V" and fs: "higher_differentiable_on V f 0"
  shows "preserves_ck_curves 0 a V f"
  unfolding preserves_ck_curves_def
proof (intro allI impI)
  fix c assume ck: "curve_ck_at 0 a c" and cv: "c a\<in>V"
  obtain S where S: "open S" "a\<in>S" "continuous_on S c"
    using ck unfolding curve_ck_at_def by (auto simp: higher_differentiable_on.simps)
  have op: "open (S \<inter> vimage c V)"
    using continuous_on_open_vimage[OF S(1), of c] S(3) V by (simp add: Int_commute)
  have cont: "continuous_on (S \<inter> vimage c V) (f \<circ> c)"
    unfolding o_def by (rule continuous_on_compose2[where t=V])
      (use fs continuous_on_subset[OF S(3), of "S \<inter> vimage c V"] in \<open>auto simp: higher_differentiable_on.simps\<close>)
  show "curve_ck_at 0 a (f \<circ> c)"
    unfolding curve_ck_at_def using S(2) cv op cont by (auto simp: higher_differentiable_on.simps)
qed

lemma local_inverse_linear_model:
  fixes f :: "'e::real_normed_vector \<Rightarrow> 'f::real_normed_vector"
  assumes W: "open W" and y: "y\<in>W"
    and fd: "f differentiable (at (g y))" and gd: "g differentiable (at y)"
    and right: "\<forall>z\<in>W. f (g z)=z"
  shows "bounded_linear (frechet_derivative g (at y)) \<and>
    bounded_linear (frechet_derivative f (at (g y))) \<and>
    (\<forall>z. frechet_derivative f (at (g y)) (frechet_derivative g (at y) z)=z)"
proof -
  have F: "bounded_linear (frechet_derivative g (at y))"
    by (rule has_derivative_bounded_linear) (use gd frechet_derivative_works in blast)
  have G: "bounded_linear (frechet_derivative f (at (g y)))"
    by (rule has_derivative_bounded_linear) (use fd frechet_derivative_works in blast)
  have diff: "(f \<circ> g) differentiable (at y)" by (rule differentiable_chain_at[OF gd fd])
  have ident: "frechet_derivative (f \<circ> g) (at y) = id"
    using frechet_derivative_transform_within_open_ext[OF diff W y, of id] right by auto
  have chain: "frechet_derivative (f \<circ> g) (at y) =
    frechet_derivative f (at (g y)) \<circ> frechet_derivative g (at y)"
    by (rule frechet_derivative_compose[OF gd fd])
  show ?thesis using F G ident chain by (auto simp: fun_eq_iff)
qed

lemma finite_source_lift_bijective:
  fixes f :: "'e::euclidean_space \<Rightarrow> 'f::real_normed_vector"
  assumes ov: "open V" and ow: "open W"
    and fs: "higher_differentiable_on V f k" and gs: "higher_differentiable_on W g k"
    and li: "\<forall>x\<in>V. g (f x)=x" and ri: "\<forall>y\<in>W. f (g y)=y"
    and j: "value_acts k a V W f J" and h: "value_acts k a W V g K"
  shows "bij_betw J (jet_domain k V) (jet_domain k W)"
proof (cases "W={}")
  case True
  have "V={}" using j True by (auto simp: value_acts_def)
  then show ?thesis using True by (simp add: jet_domain_def bij_betw_def)
next
  case False
  have forward: "preserves_ck_curves k a V f"
    by (rule euclidean_value_map_preserves_curves[OF ov fs])
  have backward: "preserves_ck_curves k a W g"
  proof (cases k)
    case 0
    show ?thesis using zero_order_preserves_curves[OF ow] gs 0 by simp
  next
    case (Suc n)
    obtain y where y: "y\<in>W" using False by blast
    have gv: "g y\<in>V" using h y by (auto simp: value_acts_def)
    have fd: "f differentiable (at (g y))" using fs gv Suc by (auto simp: higher_differentiable_on.simps)
    have gd: "g differentiable (at y)" using gs y Suc by (auto simp: higher_differentiable_on.simps)
    have model: "bounded_linear (frechet_derivative g (at y)) \<and>
      bounded_linear (frechet_derivative f (at (g y))) \<and>
      (\<forall>z. frechet_derivative f (at (g y)) (frechet_derivative g (at y) z)=z)"
      by (rule local_inverse_linear_model[OF ow y fd gd ri])
    show ?thesis
      by (rule linear_euclidean_model_preserves_curves[OF model[THEN conjunct1]
        model[THEN conjunct2, THEN conjunct1] _ ow gs])
        (use model in blast)
  qed
  show ?thesis by (rule lift_bijective_from_curve_preservation[OF ov ow forward backward li ri j h])
qed

lemma finite_source_value_relation_image:
  fixes f :: "'e::euclidean_space \<Rightarrow> 'f::real_normed_vector"
  assumes valid: "value_change_valid k U V W f g J K"
    and src: "Rel\<subseteq>U\<times>jet_domain k V" and dst: "Target\<subseteq>U\<times>jet_domain k W"
    and cov: "\<forall>p\<in>U\<times>jet_domain k V. p\<in>Rel \<longleftrightarrow> value_jet_map J p\<in>Target"
  shows "image (value_jet_map J) Rel=Target"
proof -
  have fibers: "bij_betw (J a) (jet_domain k V) (jet_domain k W)" if "a\<in>U" for a
    by (rule finite_source_lift_bijective[where f=f and g=g and K="K a"])
      (use valid that in \<open>auto simp: value_change_valid_def\<close>)
  have base: "bij_betw id U U" by simp
  have bij: "bij_betw (value_jet_map J) (U\<times>jet_domain k V) (U\<times>jet_domain k W)"
    using base_and_fiber_bijective[OF base, of J "jet_domain k V" "jet_domain k W"] fibers
    by (simp add: value_jet_map_def)
  show ?thesis by (rule value_relation_image_from_bijection[OF bij src dst cov])
qed

ML \<open>
val roots = @{thms zero_order_preserves_curves local_inverse_linear_model
  finite_source_lift_bijective finite_source_value_relation_image};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
