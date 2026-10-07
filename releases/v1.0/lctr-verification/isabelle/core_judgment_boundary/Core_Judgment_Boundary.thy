theory Core_Judgment_Boundary
 imports "LCTR_Core_Native_Law_Family.Core_Native_Law_Family"
 "LCTR_Core_Continuum_Datum.Core_Continuum_Datum"
 "LCTR_Core_Differential_Failure.Core_Differential_Failure"
begin

lemma law3_trajectory_membership:
 "Core_Native_Law_Family.condition d Law3 \<longleftrightarrow>
 K1 d \<and> (\<forall>a\<in>law_indices d. generated_member(components d a))"
 by (simp add: K3_def)
lemma law4_relation_reexpression:
 "Core_Native_Law_Family.condition d Law4 \<longleftrightarrow>
 (\<forall>f. typed_reindex_family d f \<longrightarrow> faithful_family d f \<longrightarrow>
 (\<forall>a\<in>law_indices d. image_invariant(components d a)(f a)))"
 by (simp add: K4_def)
lemma differential3_jet_membership:
 "Core_Differential_Failure.condition d N3 \<longleftrightarrow>
 (\<forall>r\<in>space d. jet d r \<and> member d r)" by simp
lemma differential4_value_covariance:
 "Core_Differential_Failure.condition d N4 \<longleftrightarrow>
 (\<forall>r\<in>space d. atlas d r \<and> valueCov d r)" by simp
lemma differential5_time_covariance:
 "Core_Differential_Failure.condition d N5 \<longleftrightarrow>
 (\<forall>r\<in>space d. \<forall>s\<in>space d. atlas d r \<and> atlas d s \<and> timeCov d r s)" by simp
lemma approximation_quantitative:
 "i<6 \<Longrightarrow> (actual p i \<longleftrightarrow> first_defect p i\<le>packet_tolerance p i)"
 by (simp add: actual_def)
lemma approximation7_extension: "actual p 6 \<longleftrightarrow> extension(packet_maps p)"
 by (simp add: actual_def)
lemma approximation8_order: "actual p 7 \<longleftrightarrow> order_condition(packet_maps p)"
 by (simp add: actual_def)
lemma approximation9_relation: "actual p 8 \<longleftrightarrow> relation_condition(packet_relations p)"
 by (simp add: actual_def)

definition approx_complete where
 "approx_complete p \<longleftrightarrow> packet_valid p \<and> (\<forall>i<9. actual p i)"
definition diff_complete where
 "diff_complete d \<longleftrightarrow> (\<forall>i. Core_Differential_Failure.condition d i)"
definition component_bridge where
 "component_bridge p d source \<longleftrightarrow> (\<forall>i. source i<9 \<and>
 (actual p (source i) \<longrightarrow> Core_Differential_Failure.condition d i))"
lemma component_bridge_suffices:
 "component_bridge p d source \<Longrightarrow> approx_complete p \<Longrightarrow> diff_complete d"
 unfolding component_bridge_def approx_complete_def diff_complete_def by blast

definition complete_differential :: "unit native" where
 "complete_differential=\<lparr>space=UNIV,atlas=(\<lambda>_. True),jet=(\<lambda>_. True),
 member=(\<lambda>_. True),valueCov=(\<lambda>_. True),timeCov=(\<lambda>_ _. True)\<rparr>"
lemma complete_differential_control: "diff_complete complete_differential"
 unfolding diff_complete_def
 by (simp add: Core_Differential_Failure.all_conditions_complete complete_differential_def)
lemma incomplete_differential_control: "\<not>diff_complete independentJet"
 unfolding diff_complete_def
 by (simp add: Core_Differential_Failure.all_conditions_complete independentJet_def)
lemma same_approximation_different_differential_results:
 "approx_complete p \<Longrightarrow>
 (approx_complete p \<and> diff_complete complete_differential) \<and>
 (approx_complete p \<and> \<not>diff_complete independentJet)"
 using complete_differential_control incomplete_differential_control by blast
lemma no_unconditional_transfer:
 "approx_complete p \<Longrightarrow> \<not>(\<forall>d::unit native. approx_complete p \<longrightarrow> diff_complete d)"
 using incomplete_differential_control by blast
lemma inconsistent_bridge_rejected:
 "approx_complete p \<Longrightarrow> \<not>(\<exists>source. component_bridge p independentJet source)"
 using component_bridge_suffices incomplete_differential_control by blast
lemma jet_membership_native_domain:
 "Core_Differential_Failure.condition d N3 \<Longrightarrow> Core_Differential_Failure.condition d N2"
 by auto

ML \<open>
val roots = @{thms law3_trajectory_membership law4_relation_reexpression
 differential3_jet_membership differential4_value_covariance differential5_time_covariance
 approximation_quantitative approximation7_extension approximation8_order approximation9_relation
 component_bridge_suffices complete_differential_control incomplete_differential_control
 same_approximation_different_differential_results no_unconditional_transfer
 inconsistent_bridge_rejected jet_membership_native_domain};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
