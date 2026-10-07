theory Core_Transported_Law_Charts
  imports "LCTR_Core_Law_Component_Charts.Core_Law_Component_Charts"
    "LCTR_Core_Law_Transport.Core_Law_Transport"
begin

definition pushed_value where "pushed_value g v = v \<circ> g"
definition pushed_curve where
  "pushed_curve J tc ic oc fin fout f g i theta =
    (ic i (fin (g (inv_into (f ` J i) (tc i \<circ> g) theta))),
     oc i (fout (g (inv_into (f ` J i) (tc i \<circ> g) theta))))"

locale transported_coordinate_atlas =
  original: coordinate_atlas E Charts TD TT ID IT OD OT tc ic oc fin fout +
  reindex: carrier_bijection E U f g
  for E :: "'t set" and Charts :: "'i set"
    and TD :: "'i\<Rightarrow>'t set" and TT :: "'i\<Rightarrow>'theta set"
    and ID :: "'i\<Rightarrow>'vin set" and IT :: "'i\<Rightarrow>'nin set"
    and OD :: "'i\<Rightarrow>'vout set" and OT :: "'i\<Rightarrow>'nout set"
    and tc :: "'i\<Rightarrow>'t\<Rightarrow>'theta"
    and ic :: "'i\<Rightarrow>'vin\<Rightarrow>'nin" and oc :: "'i\<Rightarrow>'vout\<Rightarrow>'nout"
    and fin :: "'t\<Rightarrow>'vin" and fout :: "'t\<Rightarrow>'vout"
    and U :: "'u set" and f :: "'t\<Rightarrow>'u" and g :: "'u\<Rightarrow>'t"
begin
definition pushed_time_domain where "pushed_time_domain i = {u\<in>U. g u\<in>TD i}"
definition pushed_time_coordinate where "pushed_time_coordinate i = tc i \<circ> g"

sublocale reverse: carrier_bijection U E g f
proof
  show "g ` U\<subseteq>E" by (fact reindex.inverse_typed)
  show "f ` E\<subseteq>U" by (fact reindex.forward_typed)
  show "\<And>u. u\<in>U \<Longrightarrow> f (g u)=u" by (fact reindex.right_inverse)
  show "\<And>t. t\<in>E \<Longrightarrow> g (f t)=t" by (fact reindex.left_inverse)
qed

lemma pushed_time_domain_image:
  "i\<in>Charts \<Longrightarrow> pushed_time_domain i = f ` TD i"
  unfolding pushed_time_domain_def
  using reindex.image_as_inverse[OF original.time_domain] by simp

lemma inverse_restricted_bijection:
  assumes s: "S\<subseteq>E"
  shows "bij_betw g (f ` S) S"
proof -
  have image: "g ` (f ` S)=S" by (rule reindex.inverse_image[OF s])
  have sub: "f ` S\<subseteq>U" using s reindex.forward_typed by blast
  have inj: "inj_on g (f ` S)" by (rule inj_on_subset[OF reverse.injective sub])
  show ?thesis using image inj by (simp add: bij_betw_def)
qed

sublocale pushed: coordinate_atlas U Charts pushed_time_domain TT ID IT OD OT
  pushed_time_coordinate ic oc "pushed_value g fin" "pushed_value g fout"
proof
  fix i assume i: "i\<in>Charts"
  have g: "bij_betw g (f ` TD i) (TD i)"
    by (rule inverse_restricted_bijection[OF original.time_domain[OF i]])
  show "bij_betw (pushed_time_coordinate i) (pushed_time_domain i) (TT i)"
    using bij_betw_trans[OF g original.time_chart[OF i]]
    by (simp add: pushed_time_coordinate_def pushed_time_domain_image[OF i])
next
  show "\<And>i. i\<in>Charts \<Longrightarrow> bij_betw (ic i) (ID i) (IT i)" by (rule original.input_chart)
next
  show "\<And>i. i\<in>Charts \<Longrightarrow> bij_betw (oc i) (OD i) (OT i)" by (rule original.output_chart)
next
  show "\<And>i. i\<in>Charts \<Longrightarrow> pushed_time_domain i\<subseteq>U" by (auto simp: pushed_time_domain_def)
next
  fix u assume u: "u\<in>U"
  have ge: "g u\<in>E" using reindex.inverse_typed u by blast
  obtain i where i: "i\<in>Charts" "g u\<in>TD i" "fin (g u)\<in>ID i" "fout (g u)\<in>OD i"
    using original.coverage[OF ge] by blast
  show "\<exists>i\<in>Charts. u\<in>pushed_time_domain i \<and> pushed_value g fin u\<in>ID i \<and> pushed_value g fout u\<in>OD i"
    using i u by (auto simp: pushed_time_domain_def pushed_value_def)
qed

lemma joint_domain_subset:
  "i\<in>Charts \<Longrightarrow> original.joint i\<subseteq>E"
  using original.time_domain by (auto simp: original.joint_def)

lemma pushed_joint_image:
  assumes i: "i\<in>Charts"
  shows "pushed.joint i = f ` original.joint i"
  using reindex.image_as_inverse[OF joint_domain_subset[OF i]]
  apply (simp only: pushed.joint_def original.joint_def)
  by (auto simp: pushed_time_domain_def pushed_value_def)

lemma joint_lift_typed:
  "i\<in>Charts \<Longrightarrow> t\<in>original.joint i \<Longrightarrow> f t\<in>pushed.joint i"
  by (simp add: pushed_joint_image)

lemma joint_unlift_typed:
  "u\<in>pushed.joint i \<Longrightarrow> g u\<in>original.joint i"
  apply (simp only: pushed.joint_def original.joint_def)
  by (auto simp: pushed_time_domain_def pushed_value_def)

lemma joint_lift_inverse:
  "i\<in>Charts \<Longrightarrow> t\<in>original.joint i \<Longrightarrow> g (f t)=t"
  using joint_domain_subset reindex.left_inverse by blast

lemma joint_unlift_inverse:
  "u\<in>pushed.joint i \<Longrightarrow> f (g u)=u"
  apply (simp only: pushed.joint_def)
  using reindex.right_inverse by (auto simp: pushed_time_domain_def)

lemma numeric_time_preserved:
  "i\<in>Charts \<Longrightarrow> t\<in>original.joint i \<Longrightarrow> pushed_time_coordinate i (f t)=tc i t"
  by (simp add: pushed_time_coordinate_def joint_lift_inverse)

lemma numeric_domain_preserved:
  assumes i: "i\<in>Charts"
  shows "pushed.numeric i = original.numeric i"
proof -
  have eq: "(\<lambda>t. pushed_time_coordinate i (f t)) ` original.joint i = tc i ` original.joint i"
    by (rule image_cong[OF refl]) (rule numeric_time_preserved[OF i])
  show ?thesis using eq by (simp add: pushed.numeric_def original.numeric_def pushed_joint_image[OF i] image_image)
qed

lemma native_curve_preserved:
  assumes i: "i\<in>Charts" and t: "t\<in>original.joint i"
  shows "pushed.curve i (pushed_time_coordinate i (f t)) = original.curve i (tc i t)"
proof -
  have ft: "f t\<in>pushed.joint i" by (rule joint_lift_typed[OF i t])
  have eq: "g (f t)=t" by (rule joint_lift_inverse[OF i t])
  show ?thesis using pushed.coordinate_curve_generated[OF i ft] original.coordinate_curve_generated[OF i t]
    unfolding pushed.source_values_def original.source_values_def
    by (simp add: pushed_value_def eq)
qed

lemma pushed_curve_formula:
  assumes i: "i\<in>Charts"
  shows "pushed.curve i theta = pushed_curve original.joint tc ic oc fin fout f g i theta"
  using pushed_joint_image[OF i]
  unfolding pushed.curve_def pushed.source_values_def pushed.inverse_def pushed_curve_def
  by (simp add: pushed_time_coordinate_def pushed_value_def)

lemma pushed_curve_generated:
  assumes i: "i\<in>Charts" and t: "t\<in>original.joint i"
  shows "pushed_curve original.joint tc ic oc fin fout f g i (tc i t) = original.curve i (tc i t)"
  using native_curve_preserved[OF i t] numeric_time_preserved[OF i t] pushed_curve_formula[OF i]
  by simp
end

lemma same_transported_input:
  "input_value (component_transport f g c) u = pushed_value g (input_value c) u"
  by (simp add: component_transport_def pushed_value_def)
lemma same_transported_output:
  "output_value (component_transport f g c) u = pushed_value g (output_value c) u"
  by (simp add: component_transport_def pushed_value_def)

context native_component_chart
begin
lemma transported_atlas_input_is_law_input:
  "pushed_value g (input_value (generated a)) u = input_value (component_transport f g (generated a)) u"
  by (simp add: same_transported_input)
lemma transported_atlas_output_is_law_output:
  "pushed_value g (output_value (generated a)) u = output_value (component_transport f g (generated a)) u"
  by (simp add: same_transported_output)

lemma transported_native_curve_agrees:
  assumes reindex: "carrier_bijection (evaluation_times a) U f g"
    and i: "i\<in>Charts" and t: "t\<in>chart.joint i"
  shows "pushed_curve chart.joint tc ic oc (input_value (generated a)) (output_value (generated a)) f g i (tc i t)
    = chart.curve i (tc i t)"
proof -
  interpret tr: transported_coordinate_atlas "evaluation_times a" Charts TD TT ID IT OD OT tc ic oc
    "input_value (generated a)" "output_value (generated a)" U f g
    by (unfold_locales; use atlas reindex in \<open>auto simp: coordinate_atlas_def carrier_bijection_def\<close>)
  show ?thesis by (rule tr.pushed_curve_generated[OF i t])
qed
end

ML \<open>
val roots = @{thms transported_coordinate_atlas.joint_lift_inverse transported_coordinate_atlas.joint_unlift_inverse
  transported_coordinate_atlas.numeric_time_preserved transported_coordinate_atlas.numeric_domain_preserved
  transported_coordinate_atlas.native_curve_preserved same_transported_input same_transported_output
  native_component_chart.transported_atlas_input_is_law_input native_component_chart.transported_atlas_output_is_law_output
  native_component_chart.transported_native_curve_agrees};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
