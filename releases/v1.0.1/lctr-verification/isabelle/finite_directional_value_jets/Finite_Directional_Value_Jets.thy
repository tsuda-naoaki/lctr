theory Finite_Directional_Value_Jets
  imports "LCTR_Value_Jet_Lift_Algebra.Value_Jet_Lift_Algebra"
begin

fun directional_Ck_on :: "nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "directional_Ck_on 0 f S = continuous_on S f"
| "directional_Ck_on (Suc k) f S = ((\<forall>x\<in>S. f differentiable (at x)) \<and>
      (\<forall>v. directional_Ck_on k (\<lambda>x. frechet_derivative f (at x) v) S))"

lemma directional_native_exact:
  "directional_Ck_on k f S \<longleftrightarrow> higher_differentiable_on S f k"
  by (induction k arbitrary: f) (simp_all add: higher_differentiable_on.simps)

lemma finite_lift_left_inverse:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes ov: "open V" and fs: "higher_differentiable_on V f k"
    and li: "\<forall>x\<in>V. g (f x)=x"
    and j: "value_acts k a V W f J" and h: "value_acts k a W V g K"
  shows "\<forall>v\<in>jet_domain k V. K (J v)=v"
  by (rule lift_left_inverse_from_curve_preservation[OF ov
    euclidean_value_map_preserves_curves[OF ov fs] li j h])

lemma finite_lift_bijective:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes ov: "open V" and ow: "open W"
    and fs: "higher_differentiable_on V f k" and gs: "higher_differentiable_on W g k"
    and li: "\<forall>x\<in>V. g (f x)=x" and ri: "\<forall>y\<in>W. f (g y)=y"
    and j: "value_acts k a V W f J" and h: "value_acts k a W V g K"
  shows "bij_betw J (jet_domain k V) (jet_domain k W)"
  by (rule lift_bijective_from_curve_preservation[OF ov ow
    euclidean_value_map_preserves_curves[OF ov fs]
    euclidean_value_map_preserves_curves[OF ow gs] li ri j h])

lemma finite_lift_composition:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes ov: "open V" and fs: "higher_differentiable_on V f k"
    and j: "value_acts k a V W f J" and h: "value_acts k a W Z g K"
    and hh: "value_acts k a V Z (g \<circ> f) H"
  shows "\<forall>v\<in>jet_domain k V. (K \<circ> J) v=H v"
  by (rule lift_composition_from_curve_preservation[OF
    euclidean_value_map_preserves_curves[OF ov fs] j h hh])

lemma finite_value_jet_relation_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes ov: "open V" and ow: "open W"
    and fs: "higher_differentiable_on V f k" and gs: "higher_differentiable_on W g k"
    and li: "\<forall>x\<in>V. g (f x)=x" and ri: "\<forall>y\<in>W. f (g y)=y"
    and j: "value_acts k a V W f J" and h: "value_acts k a W V g K"
    and src: "Rel\<subseteq>jet_domain k V" and dst: "Target\<subseteq>jet_domain k W"
    and cov: "\<forall>v\<in>jet_domain k V. v\<in>Rel \<longleftrightarrow> J v\<in>Target"
  shows "J ` Rel=Target"
proof -
  have onto: "J ` jet_domain k V=jet_domain k W"
    using finite_lift_bijective[OF ov ow fs gs li ri j h] by (simp add: bij_betw_def)
  show ?thesis by (rule Value_Jet_Lift_Algebra.relation_image[OF onto src dst cov])
qed

lemma trivial_source_preserves_curves:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes trivial: "\<forall>x::'a. x=0"
  shows "preserves_ck_curves k a V f"
proof -
  have eq: "f \<circ> c=(\<lambda>_. f 0)" for c :: "real\<Rightarrow>'a"
  proof (rule ext)
    fix x
    have cx: "c x=(0::'a)" using trivial by blast
    show "(f \<circ> c) x=(\<lambda>_. f 0) x" using arg_cong[OF cx, of f] by simp
  qed
  have ck: "curve_ck_at k a (f \<circ> c)" for c :: "real\<Rightarrow>'a"
    unfolding eq curve_ck_at_def
    by (intro exI[of _ UNIV]) (simp add: higher_differentiable_on_const)
  show ?thesis using ck unfolding preserves_ck_curves_def by blast
qed

lemma trivial_target_preserves_curves:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes trivial: "\<forall>y::'b. y=0"
  shows "preserves_ck_curves k a V f"
proof -
  have eq: "f \<circ> c=(\<lambda>_. 0)" for c :: "real\<Rightarrow>'a"
  proof (rule ext)
    fix x
    have fx: "f (c x)=(0::'b)" using trivial by blast
    show "(f \<circ> c) x=(\<lambda>_. 0) x" using fx by simp
  qed
  have ck: "curve_ck_at k a (f \<circ> c)" for c :: "real\<Rightarrow>'a"
    unfolding eq curve_ck_at_def
    by (intro exI[of _ UNIV]) (simp add: higher_differentiable_on_const)
  show ?thesis using ck unfolding preserves_ck_curves_def by blast
qed

lemma empty_source_preserves_curves: "preserves_ck_curves k a {} f"
  by (simp add: preserves_ck_curves_def)

lemma trivial_endpoint_lift_bijective:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes trivial: "(\<forall>x::'a. x=0) \<or> (\<forall>y::'b. y=0)"
    and ov: "open V" and ow: "open W"
    and li: "\<forall>x\<in>V. g (f x)=x" and ri: "\<forall>y\<in>W. f (g y)=y"
    and j: "value_acts k a V W f J" and h: "value_acts k a W V g K"
  shows "bij_betw J (jet_domain k V) (jet_domain k W)"
proof -
  have both: "preserves_ck_curves k a V f \<and> preserves_ck_curves k a W g"
  proof (cases "\<forall>x::'a. x=0")
    case True
    show ?thesis by (intro conjI)
      (rule trivial_source_preserves_curves[OF True], rule trivial_target_preserves_curves[OF True])
  next
    case False
    have T: "\<forall>y::'b. y=0" using trivial False by blast
    show ?thesis by (intro conjI)
      (rule trivial_target_preserves_curves[OF T], rule trivial_source_preserves_curves[OF T])
  qed
  show ?thesis by (rule lift_bijective_from_curve_preservation[OF ov ow both(1)[THEN conjunct1]
    both(1)[THEN conjunct2] li ri j h])
qed

ML \<open>
val roots = @{thms directional_native_exact finite_lift_left_inverse finite_lift_bijective
  finite_lift_composition finite_value_jet_relation_image trivial_source_preserves_curves
  trivial_target_preserves_curves empty_source_preserves_curves trivial_endpoint_lift_bijective};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
