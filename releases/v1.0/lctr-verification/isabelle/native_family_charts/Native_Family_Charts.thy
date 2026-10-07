theory Native_Family_Charts
  imports "LCTR_Native_Family_Values.Native_Family_Values"
    "LCTR_Native_Atlas_Carriers.Native_Atlas_Carriers"
    "LCTR_Core_Native_Differential_Predicates.Core_Native_Differential_Predicates"
    "LCTR_Core_Native_Time_Conditions.Core_Native_Time_Conditions"
begin

locale native_family_component_atlas =
  generated_law_representations C D B R Bind source_order rho0 d
  for C :: "'c set" and D :: "'d set" and B :: "'b set"
    and R :: "('c \<times> 'd \<times> 'b) set"
    and Bind :: "(('c \<times> 'd \<times> 'b) \<times> ('c \<times> 'd \<times> 'b)) set"
    and source_order :: "('c \<times> 'c) set" and rho0 :: "'c set set \<Rightarrow> real"
    and d :: "(real,'a,'x,'y) law_family" +
  fixes a :: 'a and k :: nat
    and TD TT :: "('c set set \<Rightarrow> real) \<Rightarrow> 'ti \<Rightarrow> real set"
    and tc :: "('c set set \<Rightarrow> real) \<Rightarrow> 'ti \<Rightarrow> real \<Rightarrow> real"
    and ID :: "'bi \<Rightarrow> 'x set" and IT :: "'bi \<Rightarrow> 'e::real_normed_vector set"
    and ic :: "'bi \<Rightarrow> 'x \<Rightarrow> 'e"
    and OD :: "'bo \<Rightarrow> 'y set" and OT :: "'bo \<Rightarrow> 'f::real_normed_vector set"
    and oc :: "'bo \<Rightarrow> 'y \<Rightarrow> 'f"
  assumes component_index: "a\<in>law_indices d"
    and positive_order: "0<k"
    and time_charts: "\<And>rho alpha. rho\<in>Reps \<Longrightarrow>
      bij_betw (tc rho alpha) (TD rho alpha) (TT rho alpha)"
    and time_domains: "\<And>rho alpha. rho\<in>Reps \<Longrightarrow> TD rho alpha\<subseteq>eval_at rho a"
    and input_charts: "\<And>beta. bij_betw (ic beta) (ID beta) (IT beta)"
    and output_charts: "\<And>gamma. bij_betw (oc gamma) (OD gamma) (OT gamma)"
    and time_open: "\<And>rho alpha. rho\<in>Reps \<Longrightarrow> open (TT rho alpha)"
    and input_open: "\<And>beta. open (IT beta)"
    and output_open: "\<And>gamma. open (OT gamma)"
    and covered: "\<And>rho t. rho\<in>Reps \<Longrightarrow> t\<in>eval_at rho a \<Longrightarrow>
      \<exists>alpha beta gamma. t\<in>TD rho alpha \<and> input_at rho a t\<in>ID beta \<and> output_at rho a t\<in>OD gamma"
begin

definition Joint where
  "Joint rho alpha beta gamma = {t\<in>TD rho alpha.
    input_at rho a t\<in>ID beta \<and> output_at rho a t\<in>OD gamma}"
definition Numeric where "Numeric rho alpha beta gamma = image (tc rho alpha) (Joint rho alpha beta gamma)"
definition Curve where
  "Curve rho alpha beta gamma theta =
    (ic beta (input_at rho a (inv_into (Joint rho alpha beta gamma) (tc rho alpha) theta)),
     oc gamma (output_at rho a (inv_into (Joint rho alpha beta gamma) (tc rho alpha) theta)))"
definition Diff2 where
  "Diff2 rho alpha beta gamma \<longleftrightarrow>
    native_diff2 (Numeric rho alpha beta gamma) (Curve rho alpha beta gamma) k"
definition Pair where
  "Pair rho alpha beta gamma theta =
    canonical_pair (Numeric rho alpha beta gamma) (Curve rho alpha beta gamma) k theta"
definition Diff3 where
  "Diff3 rho alpha beta gamma Rel \<longleftrightarrow>
    native_diff3 (Numeric rho alpha beta gamma) (Curve rho alpha beta gamma) k Rel"

lemma actual_component_atlas:
  assumes rep: "rho\<in>Reps"
  shows "coordinate_atlas (eval_at rho a) (UNIV::('ti\<times>'bi\<times>'bo) set)
    (\<lambda>i. TD rho (fst i)) (\<lambda>i. TT rho (fst i))
    (\<lambda>i. ID (fst (snd i))) (\<lambda>i. IT (fst (snd i)))
    (\<lambda>i. OD (snd (snd i))) (\<lambda>i. OT (snd (snd i)))
    (\<lambda>i. tc rho (fst i)) (\<lambda>i. ic (fst (snd i))) (\<lambda>i. oc (snd (snd i)))
    (input_at rho a) (output_at rho a)"
  unfolding coordinate_atlas_def
  using time_charts[OF rep] time_domains[OF rep] input_charts output_charts covered[OF rep]
  by auto

lemma actual_product_atlas:
  "rho\<in>Reps \<Longrightarrow>
    native_product_atlas (TT rho) (TD rho) (tc rho) IT ID ic OT OD oc"
  unfolding native_product_atlas_def
  using time_charts input_charts output_charts by blast

lemma same_generated_law_values:
  "input_at rho a t = input_value (component_at rho a) t \<and>
    output_at rho a t = output_value (component_at rho a) t"
  by (simp add: input_at_def output_at_def component_at_def component_transport_def)

lemma joint_domain_coverage:
  "rho\<in>Reps \<Longrightarrow> t\<in>eval_at rho a \<Longrightarrow>
    \<exists>alpha beta gamma. t\<in>Joint rho alpha beta gamma"
  using covered by (auto simp: Joint_def)

lemma numeric_domain_bijective:
  assumes rep: "rho\<in>Reps"
  shows "bij_betw (tc rho alpha) (Joint rho alpha beta gamma) (Numeric rho alpha beta gamma)"
proof -
  have inj: "inj_on (tc rho alpha) (TD rho alpha)"
    using time_charts[OF rep] by (simp add: bij_betw_def)
  have sub: "Joint rho alpha beta gamma\<subseteq>TD rho alpha" by (auto simp: Joint_def)
  have "inj_on (tc rho alpha) (Joint rho alpha beta gamma)" by (rule inj_on_subset[OF inj sub])
  then show ?thesis by (simp add: bij_betw_def Numeric_def)
qed

lemma actual_coordinate_values:
  assumes rep: "rho\<in>Reps" and t: "t\<in>Joint rho alpha beta gamma"
  shows "Curve rho alpha beta gamma (tc rho alpha t)=
    (ic beta (input_value (component_at rho a) t), oc gamma (output_value (component_at rho a) t))"
proof -
  have bij: "bij_betw (tc rho alpha) (Joint rho alpha beta gamma) (Numeric rho alpha beta gamma)"
    by (rule numeric_domain_bijective[OF rep])
  have inverse: "inv_into (Joint rho alpha beta gamma) (tc rho alpha) (tc rho alpha t)=t"
    by (rule bij_betw_inv_into_left[OF bij t])
  show ?thesis
    by (simp add: Curve_def inverse same_transported_input_value same_transported_output_value)
qed

lemma numeric_curve_typed:
  assumes rep: "rho\<in>Reps" and theta: "theta\<in>Numeric rho alpha beta gamma"
  shows "Curve rho alpha beta gamma theta\<in>IT beta\<times>OT gamma"
proof -
  obtain t where t: "t\<in>Joint rho alpha beta gamma" and theta_eq: "theta=tc rho alpha t"
    using theta unfolding Numeric_def by blast
  have vals: "input_at rho a t\<in>ID beta" "output_at rho a t\<in>OD gamma"
    using t by (auto simp: Joint_def)
  have inv: "inv_into (Joint rho alpha beta gamma) (tc rho alpha) (tc rho alpha t)=t"
    by (rule bij_betw_inv_into_left[OF numeric_domain_bijective[OF rep] t])
  show ?thesis using vals input_charts[of beta] output_charts[of gamma]
    by (auto simp: theta_eq Curve_def inv bij_betw_def)
qed

lemma shared_value_charts_between:
  fixes rho sigma :: "'c set set \<Rightarrow> real"
  assumes r: "rho\<in>Reps" and s: "sigma\<in>Reps"
    and t: "t\<in>TD rho alpha" and moved: "between rho sigma t\<in>TD sigma delta"
  shows "t\<in>Joint rho alpha beta gamma \<longleftrightarrow>
    between rho sigma t\<in>Joint sigma delta beta gamma"
proof -
  have evaluation: "t\<in>eval_at rho a" using time_domains[OF r] t by blast
  have vals: "input_at sigma a (between rho sigma t) = input_at rho a t \<and>
    output_at sigma a (between rho sigma t) = output_at rho a t"
    by (rule between_preserves_native_values[OF r s component_index evaluation])
  show ?thesis using vals t moved by (simp add: Joint_def)
qed

lemma actual_between_chart_overlap:
  fixes rho sigma :: "'c set set \<Rightarrow> real"
  assumes r: "rho\<in>Reps" and s: "sigma\<in>Reps"
  shows "coordinate_overlaps (eval_at rho a) (eval_at sigma a) (between rho sigma)
    (TD rho alpha) (TD sigma delta) (TT rho alpha) (TT sigma delta)
    (tc rho alpha) (tc sigma delta)"
proof -
  interpret tr: carrier_bijection "eval_at rho a" "eval_at sigma a"
    "between rho sigma" "between sigma rho"
    by (rule between_evaluation_bijection[OF r s component_index])
  have bij: "bij_betw (between rho sigma) (eval_at rho a) (eval_at sigma a)"
    using tr.injective tr.surjective by (simp add: bij_betw_def)
  show ?thesis unfolding coordinate_overlaps_def
    using bij time_domains[OF r] time_domains[OF s] time_charts[OF r] time_charts[OF s] by blast
qed

lemma zeroth_pair_is_generated_law:
  assumes rep: "rho\<in>Reps" and t: "t\<in>Joint rho alpha beta gamma"
  shows "snd (Pair rho alpha beta gamma (tc rho alpha t)) 0 =
    (ic beta (input_value (component_at rho a) t),oc gamma (output_value (component_at rho a) t))"
proof -
  have num: "tc rho alpha t\<in>Numeric rho alpha beta gamma" using t by (auto simp: Numeric_def)
  show ?thesis using actual_coordinate_values[OF rep t]
    by (simp add: Pair_def canonical_pair_def jet_def restrict_def total_curve_def num)
qed

lemma third_condition_exact:
  "Diff3 rho alpha beta gamma Rel \<longleftrightarrow>
    Diff2 rho alpha beta gamma \<and>
    (\<forall>theta\<in>Numeric rho alpha beta gamma. Pair rho alpha beta gamma theta\<in>Rel)"
  by (simp add: Diff3_def Diff2_def Pair_def native_diff3_def)
end

ML \<open>
val roots = @{thms native_family_component_atlas.actual_component_atlas
  native_family_component_atlas.actual_product_atlas
  native_family_component_atlas.same_generated_law_values
  native_family_component_atlas.joint_domain_coverage
  native_family_component_atlas.numeric_domain_bijective
  native_family_component_atlas.actual_coordinate_values
  native_family_component_atlas.numeric_curve_typed
  native_family_component_atlas.shared_value_charts_between
  native_family_component_atlas.actual_between_chart_overlap
  native_family_component_atlas.zeroth_pair_is_generated_law
  native_family_component_atlas.third_condition_exact};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val checked_context = Config.put show_types true @{context};
val _ = List.app (fn th => writeln ("LCTR_ROOT_STATEMENT=" ^ Thm.string_of_thm checked_context th)) roots;
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
