theory Modeled_Source_Value_Change
  imports "LCTR_Finite_Source_Value_Change.Finite_Source_Value_Change"
begin

lemma modeled_source_lift_bijective:
  fixes F :: "'e::real_normed_vector \<Rightarrow> 'z::euclidean_space"
    and G :: "'z \<Rightarrow> 'e" and f :: "'e \<Rightarrow> 'b::real_normed_vector"
  assumes F: "bounded_linear F" and G: "bounded_linear G"
    and rec: "\<And>x. G (F x) = x"
    and ov: "open V" and ow: "open W"
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
    by (rule linear_euclidean_model_preserves_curves[OF F G rec ov fs])
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
    have to: "bounded_linear (F \<circ> frechet_derivative g (at y))"
      using bounded_linear_compose[OF F model[THEN conjunct1]] by (simp add: o_def)
    have linback: "bounded_linear (frechet_derivative f (at (g y)) \<circ> G)"
      using bounded_linear_compose[OF model[THEN conjunct2, THEN conjunct1] G] by (simp add: o_def)
    have inv: "(frechet_derivative f (at (g y)) \<circ> G)
        ((F \<circ> frechet_derivative g (at y)) x)=x" for x
      using model by (simp add: rec)
    show ?thesis by (rule linear_euclidean_model_preserves_curves[OF to linback inv ow gs])
  qed
  show ?thesis by (rule lift_bijective_from_curve_preservation[OF ov ow forward backward li ri j h])
qed

lemma modeled_source_value_relation_image:
  fixes F :: "'e::real_normed_vector \<Rightarrow> 'z::euclidean_space"
    and G :: "'z \<Rightarrow> 'e" and f :: "'e \<Rightarrow> 'b::real_normed_vector"
  assumes F: "bounded_linear F" and G: "bounded_linear G" and rec: "\<And>x. G (F x) = x"
    and valid: "value_change_valid k U V W f g J K"
    and src: "Rel\<subseteq>U\<times>jet_domain k V" and dst: "Target\<subseteq>U\<times>jet_domain k W"
    and cov: "\<forall>p\<in>U\<times>jet_domain k V. p\<in>Rel \<longleftrightarrow> value_jet_map J p\<in>Target"
  shows "image (value_jet_map J) Rel=Target"
proof -
  have fibers: "bij_betw (J a) (jet_domain k V) (jet_domain k W)" if "a\<in>U" for a
    by (rule modeled_source_lift_bijective[OF F G rec, where f=f and g=g and K="K a"])
      (use valid that in \<open>auto simp: value_change_valid_def\<close>)
  have base: "bij_betw id U U" by simp
  have bij: "bij_betw (value_jet_map J) (U\<times>jet_domain k V) (U\<times>jet_domain k W)"
    using base_and_fiber_bijective[OF base, of J "jet_domain k V" "jet_domain k W"] fibers
    by (simp add: value_jet_map_def)
  show ?thesis by (rule value_relation_image_from_bijection[OF bij src dst cov])
qed

lemma modeled_native_membership:
  fixes F :: "'e::real_normed_vector \<Rightarrow> 'z::euclidean_space"
    and G :: "'z \<Rightarrow> 'e" and f :: "'e \<Rightarrow> 'b::real_normed_vector"
  assumes F: "bounded_linear F" and G: "bounded_linear G" and rec: "\<And>x. G (F x) = x"
    and valid: "value_change_valid k N V W f g J K"
    and src: "Rel\<subseteq>N\<times>jet_domain k V" and dst: "Target\<subseteq>N\<times>jet_domain k W"
    and cov: "\<forall>p\<in>N\<times>jet_domain k V. p\<in>Rel \<longleftrightarrow> value_jet_map J p\<in>Target"
    and member: "\<forall>t\<in>N. (t,zjet k t d)\<in>Rel"
  shows "image (value_jet_map J) Rel=Target \<and>
    (\<forall>t\<in>N. value_jet_map J (t,zjet k t d)\<in>Target)"
  using modeled_source_value_relation_image[OF F G rec valid src dst cov] member by blast

lemma zero_source_native_membership:
  fixes f :: "'e::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes zero: "\<forall>x::'e. x=0" and valid: "value_change_valid k N V W f g J K"
    and src: "Rel\<subseteq>N\<times>jet_domain k V" and dst: "Target\<subseteq>N\<times>jet_domain k W"
    and cov: "\<forall>p\<in>N\<times>jet_domain k V. p\<in>Rel \<longleftrightarrow> value_jet_map J p\<in>Target"
    and member: "\<forall>t\<in>N. (t,zjet k t d)\<in>Rel"
  shows "image (value_jet_map J) Rel=Target \<and>
    (\<forall>t\<in>N. value_jet_map J (t,zjet k t d)\<in>Target)"
  using trivial_value_relation_image[OF disjI1[OF zero] valid src dst cov] member by blast

ML \<open>
val roots = @{thms modeled_source_lift_bijective modeled_source_value_relation_image
  modeled_native_membership zero_source_native_membership};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
