theory Native_Family_Value_Images
  imports "LCTR_Linear_Domain_Regularity.Linear_Domain_Regularity"
    "LCTR_Native_Differential_Consequences.Native_Differential_Consequences"
begin

lemma value_map_bijective_via_euclidean_model:
  fixes F :: "'e::real_normed_vector \<Rightarrow> 'z::euclidean_space"
    and G :: "'z \<Rightarrow> 'e" and f g :: "'e \<Rightarrow> 'e"
  assumes F: "bounded_linear F" and G: "bounded_linear G" and rec: "\<And>x. G (F x) = x"
    and valid: "value_change_valid k U V W f g J K"
  shows "bij_betw (value_jet_map J) (U\<times>jet_domain k V) (U\<times>jet_domain k W)"
proof -
  have fibers: "bij_betw (J a) (jet_domain k V) (jet_domain k W)" if at: "a\<in>U" for a
  proof -
    have ov: "open V" and ow: "open W" and fs: "higher_differentiable_on V f k"
      and gs: "higher_differentiable_on W g k" and li: "\<forall>x\<in>V. g (f x) = x"
      and ri: "\<forall>y\<in>W. f (g y) = y" and ja: "value_acts k a V W f (J a)"
      and ka: "value_acts k a W V g (K a)"
      using valid at by (auto simp: value_change_valid_def)
    have fp: "preserves_ck_curves k a V f"
      by (rule linear_euclidean_model_preserves_curves[OF F G rec ov fs])
    have gp: "preserves_ck_curves k a W g"
      by (rule linear_euclidean_model_preserves_curves[OF F G rec ow gs])
    show ?thesis by (rule lift_bijective_from_curve_preservation[OF ov ow fp gp li ri ja ka])
  qed
  have base: "bij_betw id U U" by simp
  show ?thesis using base_and_fiber_bijective[OF base, of J "jet_domain k V" "jet_domain k W"]
    fibers by (simp add: value_jet_map_def)
qed

context native_family_component_atlas
begin
definition ValueOverlap where
  "ValueOverlap beta gamma = actual_overlap_image (ProductSource beta) (ProductSource gamma)
    (ProductCoordinate beta)"
definition ValueCarrier where
  "ValueCarrier rho alpha beta gamma = TT rho alpha \<times> jet_domain k (ValueOverlap beta gamma)"

lemma chosen_value_bound:
  assumes h: "Complete Rel" and rep: "rho\<in>Reps"
  shows "value_change_valid k (TT rho alpha) (ValueOverlap beta gamma) (ValueOverlap gamma beta)
    (vforward (ChosenRegular rho) alpha beta gamma) (vbackward (ChosenRegular rho) alpha beta gamma)
    (vlift (ChosenRegular rho) alpha beta gamma) (vinverse (ChosenRegular rho) alpha beta gamma)"
proof -
  interpret prod: native_product_atlas k "TT rho" "TD rho" "tc rho" IT ID ic OT OD oc
    by (rule actual_product_atlas[OF rep])
  have reg: "prod.product.regular (ChosenRegular rho)"
    using chosen_regular[OF h rep]
    by (simp only: RegularAt_def ProductTarget_def[abs_def] ProductSource_def[abs_def] ProductCoordinate_def[abs_def])
  have valid: "value_change_valid k (TT rho alpha) (prod.product.VDomain beta gamma) (prod.product.VDomain gamma beta)
    (vforward (ChosenRegular rho) alpha beta gamma) (vbackward (ChosenRegular rho) alpha beta gamma)
    (vlift (ChosenRegular rho) alpha beta gamma) (vinverse (ChosenRegular rho) alpha beta gamma)"
    using reg unfolding prod.product.regular_def prod.product.value_bound_def by blast
  show ?thesis using valid
    by (simp only: ValueOverlap_def prod.product.VDomain_def ProductSource_def[abs_def] ProductCoordinate_def[abs_def])
qed

lemma chosen_value_image_from_bijection:
  assumes h: "Complete Rel" and rep: "rho\<in>Reps"
    and bij: "bij_betw (value_jet_map (vlift (ChosenRegular rho) alpha beta gamma))
      (ValueCarrier rho alpha beta gamma) (ValueCarrier rho alpha gamma beta)"
  shows "image (value_jet_map (vlift (ChosenRegular rho) alpha beta gamma))
    (Rel rho alpha beta \<inter> ValueCarrier rho alpha beta gamma) =
    Rel rho alpha gamma \<inter> ValueCarrier rho alpha gamma beta"
proof -
  interpret prod: native_product_atlas k "TT rho" "TD rho" "tc rho" IT ID ic OT OD oc
    by (rule actual_product_atlas[OF rep])
  have carriers: "ValueCarrier rho alpha beta gamma = prod.product.VSpace alpha beta gamma"
    for alpha beta gamma
    by (simp only: ValueCarrier_def ValueOverlap_def prod.product.VSpace_def prod.product.VDomain_def
      ProductSource_def[abs_def] ProductCoordinate_def[abs_def])
  have cov: "prod.product.ValueCov (ChosenRegular rho) (Rel rho)"
    using chosen_value_covariance[OF h rep]
    by (simp only: CovAt_def ProductSource_def[abs_def] ProductCoordinate_def[abs_def])
  have mapped: "bij_betw (value_jet_map (vlift (ChosenRegular rho) alpha beta gamma))
    (prod.product.VSpace alpha beta gamma) (prod.product.VSpace alpha gamma beta)"
    using bij by (simp only: carriers)
  show ?thesis unfolding carriers
    by (rule prod.product.restriction_image_from_bijection[OF mapped cov])
qed

lemma native_value_relation_image_via_model:
  fixes F :: "('e\<times>'f) \<Rightarrow> 'z::euclidean_space" and G :: "'z \<Rightarrow> ('e\<times>'f)"
  assumes h: "Complete Rel" and rep: "rho\<in>Reps"
    and F: "bounded_linear F" and G: "bounded_linear G" and rec: "\<And>x. G (F x) = x"
  shows "image (value_jet_map (vlift (ChosenRegular rho) alpha beta gamma))
    (Rel rho alpha beta \<inter> ValueCarrier rho alpha beta gamma) =
    Rel rho alpha gamma \<inter> ValueCarrier rho alpha gamma beta"
proof -
  have valid: "value_change_valid k (TT rho alpha) (ValueOverlap beta gamma) (ValueOverlap gamma beta)
    (vforward (ChosenRegular rho) alpha beta gamma) (vbackward (ChosenRegular rho) alpha beta gamma)
    (vlift (ChosenRegular rho) alpha beta gamma) (vinverse (ChosenRegular rho) alpha beta gamma)"
    by (rule chosen_value_bound[OF h rep])
  have bij: "bij_betw (value_jet_map (vlift (ChosenRegular rho) alpha beta gamma))
    (ValueCarrier rho alpha beta gamma) (ValueCarrier rho alpha gamma beta)"
    unfolding ValueCarrier_def by (rule value_map_bijective_via_euclidean_model[OF F G rec valid])
  show ?thesis by (rule chosen_value_image_from_bijection[OF h rep bij])
qed

lemma native_value_relation_image_zero:
  assumes h: "Complete Rel" and rep: "rho\<in>Reps"
    and zi: "\<forall>x::'e. x=0" and zo: "\<forall>y::'f. y=0"
  shows "image (value_jet_map (vlift (ChosenRegular rho) alpha beta gamma))
    (Rel rho alpha beta \<inter> ValueCarrier rho alpha beta gamma) =
    Rel rho alpha gamma \<inter> ValueCarrier rho alpha gamma beta"
proof -
  have trivial: "(\<forall>p::'e\<times>'f. p=0) \<or> (\<forall>p::'e\<times>'f. p=0)"
    using zi zo by (auto intro!: prod_eqI)
  have valid: "value_change_valid k (TT rho alpha) (ValueOverlap beta gamma) (ValueOverlap gamma beta)
    (vforward (ChosenRegular rho) alpha beta gamma) (vbackward (ChosenRegular rho) alpha beta gamma)
    (vlift (ChosenRegular rho) alpha beta gamma) (vinverse (ChosenRegular rho) alpha beta gamma)"
    by (rule chosen_value_bound[OF h rep])
  have bij: "bij_betw (value_jet_map (vlift (ChosenRegular rho) alpha beta gamma))
    (ValueCarrier rho alpha beta gamma) (ValueCarrier rho alpha gamma beta)"
    unfolding ValueCarrier_def by (rule trivial_value_map_bijective[OF trivial valid])
  show ?thesis by (rule chosen_value_image_from_bijection[OF h rep bij])
qed
end

lemma positive_pair_model:
  "bounded_linear (id :: ('e::euclidean_space\<times>'f::euclidean_space) \<Rightarrow> ('e\<times>'f)) \<and>
    bounded_linear (id :: ('e\<times>'f) \<Rightarrow> ('e\<times>'f)) \<and> (\<forall>x::'e\<times>'f. id (id x) = x)"
  by (simp add: id_def)

lemma zero_left_model:
  assumes zero: "\<forall>x::'e::real_normed_vector. x=0"
  shows "bounded_linear (snd :: ('e\<times>'f::euclidean_space) \<Rightarrow> 'f) \<and>
    bounded_linear (\<lambda>y::'f. (0::'e,y)) \<and> (\<forall>x::'e\<times>'f. (0,snd x) = x)"
proof (intro conjI)
  show "bounded_linear (snd :: ('e\<times>'f) \<Rightarrow> 'f)" by (rule bounded_linear_snd)
  show "bounded_linear (\<lambda>y::'f. (0::'e,y))" by (intro bounded_linear_Pair bounded_linear_zero bounded_linear_ident)
  show "\<forall>x::'e\<times>'f. (0,snd x) = x" using zero by (auto intro!: prod_eqI)
qed

lemma zero_right_model:
  assumes zero: "\<forall>y::'f::real_normed_vector. y=0"
  shows "bounded_linear (fst :: ('e::euclidean_space\<times>'f) \<Rightarrow> 'e) \<and>
    bounded_linear (\<lambda>x::'e. (x,0::'f)) \<and> (\<forall>p::'e\<times>'f. (fst p,0) = p)"
proof (intro conjI)
  show "bounded_linear (fst :: ('e\<times>'f) \<Rightarrow> 'e)" by (rule bounded_linear_fst)
  show "bounded_linear (\<lambda>x::'e. (x,0::'f))" by (intro bounded_linear_Pair bounded_linear_ident bounded_linear_zero)
  show "\<forall>p::'e\<times>'f. (fst p,0) = p" using zero by (auto intro!: prod_eqI)
qed

ML \<open>
val roots = @{thms value_map_bijective_via_euclidean_model
  native_family_component_atlas.chosen_value_bound
  native_family_component_atlas.chosen_value_image_from_bijection
  native_family_component_atlas.native_value_relation_image_via_model
  native_family_component_atlas.native_value_relation_image_zero
  positive_pair_model zero_left_model zero_right_model};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
