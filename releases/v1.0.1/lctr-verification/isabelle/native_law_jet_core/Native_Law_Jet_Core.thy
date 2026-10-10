theory Native_Law_Jet_Core
  imports "LCTR_Core_Transported_Native_Jets.Core_Transported_Native_Jets"
    "LCTR_Value_Jet_Lift_Algebra.Value_Jet_Lift_Algebra"
begin

lemma zeroth_is_generated_curve:
  assumes d: "atlas_jet_data N q k d" and t: "t\<in>N"
  shows "zjet k t d 0=q t"
  using d t by (simp add: zjet_zeroth atlas_jet_data_def)

lemma smooth_realizations_agree_nearby:
  assumes d: "atlas_jet_data N q k d" and e: "atlas_jet_data N q k e"
    and op: "open N" and t: "t\<in>N"
  shows "eventually (\<lambda>x. d x=e x) (nhds t)"
  using eventually_nhds_in_open[OF op t]
  by eventually_elim (use d e in \<open>auto simp: atlas_jet_data_def\<close>)

lemma native_jet_independent_of_extension:
  assumes "atlas_jet_data N q k d" "atlas_jet_data N q k e" "open N" "t\<in>N"
  shows "zjet k t d=zjet k t e"
  by (rule zjet_germ[OF smooth_realizations_agree_nearby[OF assms]])

lemma generated_jet_relation_membership:
  assumes "\<forall>t\<in>N. (t,zjet k t d)\<in>Rel"
  shows "(\<lambda>t. (t,zjet k t d)) ` N \<subseteq> Rel"
  using assms by blast

context native_real_component_chart
begin

lemma input_realization_value_in_chart:
  assumes i: "i\<in>Charts" and t: "t\<in>chart.numeric i"
    and d: "atlas_jet_data (chart.numeric i) (fst \<circ> chart.curve i) k d"
  shows "d t\<in>IT i"
  using chart.curve_values_typed[OF i t] d t by (auto simp: atlas_jet_data_def)

lemma output_realization_value_in_chart:
  assumes i: "i\<in>Charts" and t: "t\<in>chart.numeric i"
    and d: "atlas_jet_data (chart.numeric i) (snd \<circ> chart.curve i) k d"
  shows "d t\<in>OT i"
  using chart.curve_values_typed[OF i t] d t by (auto simp: atlas_jet_data_def)

lemmas realization_value_in_chart = input_realization_value_in_chart output_realization_value_in_chart

lemma input_zeroth_is_native_law_value:
  assumes i: "i\<in>Charts" and t: "t\<in>chart.joint i"
    and d: "atlas_jet_data (chart.numeric i) (fst \<circ> chart.curve i) k d"
  shows "input_value (generated a) t\<in>ID i \<and>
    zjet k (tc i t) d 0 = ic i (input_value (generated a) t)"
proof -
  have ti: "tc i t\<in>chart.numeric i" using t by (auto simp: chart.numeric_def)
  have z: "zjet k (tc i t) d 0=fst (chart.curve i (tc i t))"
    using zeroth_is_generated_curve[OF d ti] by simp
  show ?thesis using native_input_curve[OF i t] z by auto
qed

lemma output_zeroth_is_native_law_value:
  assumes i: "i\<in>Charts" and t: "t\<in>chart.joint i"
    and d: "atlas_jet_data (chart.numeric i) (snd \<circ> chart.curve i) k d"
  shows "output_value (generated a) t\<in>OD i \<and>
    zjet k (tc i t) d 0 = oc i (output_value (generated a) t)"
proof -
  have ti: "tc i t\<in>chart.numeric i" using t by (auto simp: chart.numeric_def)
  have z: "zjet k (tc i t) d 0=snd (chart.curve i (tc i t))"
    using zeroth_is_generated_curve[OF d ti] by simp
  show ?thesis using native_output_curve[OF i t] z by auto
qed

lemmas zeroth_is_native_law_value = input_zeroth_is_native_law_value output_zeroth_is_native_law_value

lemma input_value_change_acts_on_native_jet:
  assumes i: "i\<in>Charts" and t: "t\<in>chart.numeric i"
    and d: "atlas_jet_data (chart.numeric i) (fst \<circ> chart.curve i) k d"
    and action: "value_acts k t (IT i) W f (J t)"
  shows "J t (zjet k t d)=zjet k t (f \<circ> d)"
proof -
  have ck: "curve_ck_at k t d" using d t by (simp add: atlas_jet_data_def)
  show ?thesis by (rule value_acts_apply[OF action ck input_realization_value_in_chart[OF i t d]])
qed

lemma output_value_change_acts_on_native_jet:
  assumes i: "i\<in>Charts" and t: "t\<in>chart.numeric i"
    and d: "atlas_jet_data (chart.numeric i) (snd \<circ> chart.curve i) k d"
    and action: "value_acts k t (OT i) W f (J t)"
  shows "J t (zjet k t d)=zjet k t (f \<circ> d)"
proof -
  have ck: "curve_ck_at k t d" using d t by (simp add: atlas_jet_data_def)
  show ?thesis by (rule value_acts_apply[OF action ck output_realization_value_in_chart[OF i t d]])
qed

lemmas value_change_acts_on_native_jet = input_value_change_acts_on_native_jet output_value_change_acts_on_native_jet
end

ML \<open>
val roots = @{thms native_real_component_chart.realization_value_in_chart zeroth_is_generated_curve
  native_real_component_chart.zeroth_is_native_law_value smooth_realizations_agree_nearby
  native_jet_independent_of_extension generated_jet_relation_membership
  native_real_component_chart.value_change_acts_on_native_jet};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
