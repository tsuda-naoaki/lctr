theory Native_Time_Change
  imports "LCTR_Native_Law_Jet_Core.Native_Law_Jet_Core"
    "LCTR_Zero_Time_Jet_Transport.Zero_Time_Jet_Transport"
begin

definition time_change_valid where
  "time_change_valid k V U W f g J K \<longleftrightarrow>
    open U \<and> open W \<and> f ` U\<subseteq>W \<and> g ` W\<subseteq>U \<and>
    higher_differentiable_on U f k \<and> higher_differentiable_on W g k \<and>
    (\<forall>x\<in>U. g (f x)=x) \<and> (\<forall>y\<in>W. f (g y)=y) \<and>
    (\<forall>a\<in>U. zero_time_acts k a (f a) V g (J a)) \<and>
    (\<forall>a\<in>U. zero_time_acts k (f a) a V f (K (f a)))"

lemma time_change_map_bijective:
  assumes "time_change_valid k V U W f g J K"
  shows "bij_betw (time_jet_map f J) (U\<times>jet_domain k V) (W\<times>jet_domain k V)"
  by (rule time_jet_map_bijective[where K=K and g=g])
     (use assms in \<open>auto simp: time_change_valid_def\<close>)

lemma time_change_relation_image:
  assumes valid: "time_change_valid k V U W f g J K"
    and src: "A\<subseteq>U\<times>jet_domain k V" and dst: "B\<subseteq>W\<times>jet_domain k V"
    and cov: "\<forall>p\<in>U\<times>jet_domain k V. p\<in>A \<longleftrightarrow> time_jet_map f J p\<in>B"
  shows "time_jet_map f J ` A=B"
  by (rule time_jet_relation_image[OF time_change_map_bijective[OF valid] src dst cov])

lemma time_change_preserves_zeroth:
  assumes valid: "time_change_valid k V U W f g J K"
    and t: "t\<in>U" and v: "v\<in>jet_domain k V"
  shows "snd (time_jet_map f J (t,v)) 0=v 0"
proof -
  have act: "zero_time_acts k t (f t) V g (J t)"
    using valid t unfolding time_change_valid_def by blast
  show ?thesis using time_jet_zeroth_preserved[OF act v] by (simp add: time_jet_map_def)
qed

lemma native_time_covariance:
  assumes valid: "time_change_valid k V N W f g J K"
    and src: "A\<subseteq>N\<times>jet_domain k V" and dst: "B\<subseteq>W\<times>jet_domain k V"
    and cov: "\<forall>p\<in>N\<times>jet_domain k V. p\<in>A \<longleftrightarrow> time_jet_map f J p\<in>B"
    and member: "\<forall>t\<in>N. (t,zjet k t d)\<in>A"
  shows "time_jet_map f J ` A=B \<and> (\<forall>t\<in>N. time_jet_map f J (t,zjet k t d)\<in>B)"
  by (rule time_native_membership_preserved[OF time_change_relation_image[OF valid src dst cov] member])

context native_real_component_chart
begin

lemma input_time_change_preserves_native_zeroth:
  assumes i: "i\<in>Charts" and t: "t\<in>chart.numeric i"
    and d: "atlas_jet_data (chart.numeric i) (fst \<circ> chart.curve i) k d"
    and change: "time_change_valid k (IT i) (chart.numeric i) W f g J K"
  shows "snd (time_jet_map f J (t,zjet k t d)) 0 = fst (chart.curve i t)"
proof -
  have typed: "zjet k t d\<in>jet_domain k (IT i)"
    by (rule zjet_in_domain[where f=d and a=t and k=k, OF input_realization_value_in_chart[OF i t d]])
  have eq: "zjet k t d 0 = fst (chart.curve i t)"
    using zeroth_is_generated_curve[OF d t] by simp
  show ?thesis using time_change_preserves_zeroth[OF change t typed] eq by simp
qed

lemma output_time_change_preserves_native_zeroth:
  assumes i: "i\<in>Charts" and t: "t\<in>chart.numeric i"
    and d: "atlas_jet_data (chart.numeric i) (snd \<circ> chart.curve i) k d"
    and change: "time_change_valid k (OT i) (chart.numeric i) W f g J K"
  shows "snd (time_jet_map f J (t,zjet k t d)) 0 = snd (chart.curve i t)"
proof -
  have typed: "zjet k t d\<in>jet_domain k (OT i)"
    by (rule zjet_in_domain[where f=d and a=t and k=k, OF output_realization_value_in_chart[OF i t d]])
  have eq: "zjet k t d 0 = snd (chart.curve i t)"
    using zeroth_is_generated_curve[OF d t] by simp
  show ?thesis using time_change_preserves_zeroth[OF change t typed] eq by simp
qed

lemmas time_change_preserves_native_zeroth = input_time_change_preserves_native_zeroth output_time_change_preserves_native_zeroth

lemma input_time_covariance_preserves_native_membership:
  assumes valid: "time_change_valid k (IT i) (chart.numeric i) W f g J K"
    and src: "A\<subseteq>chart.numeric i\<times>jet_domain k (IT i)"
    and dst: "Target\<subseteq>W\<times>jet_domain k (IT i)"
    and cov: "\<forall>p\<in>chart.numeric i\<times>jet_domain k (IT i). p\<in>A \<longleftrightarrow> time_jet_map f J p\<in>Target"
    and member: "\<forall>t\<in>chart.numeric i. (t,zjet k t d)\<in>A"
  shows "time_jet_map f J ` A=Target \<and>
    (\<forall>t\<in>chart.numeric i. time_jet_map f J (t,zjet k t d)\<in>Target)"
  by (rule native_time_covariance[OF valid src dst cov member])

lemma output_time_covariance_preserves_native_membership:
  assumes valid: "time_change_valid k (OT i) (chart.numeric i) W f g J K"
    and src: "A\<subseteq>chart.numeric i\<times>jet_domain k (OT i)"
    and dst: "Target\<subseteq>W\<times>jet_domain k (OT i)"
    and cov: "\<forall>p\<in>chart.numeric i\<times>jet_domain k (OT i). p\<in>A \<longleftrightarrow> time_jet_map f J p\<in>Target"
    and member: "\<forall>t\<in>chart.numeric i. (t,zjet k t d)\<in>A"
  shows "time_jet_map f J ` A=Target \<and>
    (\<forall>t\<in>chart.numeric i. time_jet_map f J (t,zjet k t d)\<in>Target)"
  by (rule native_time_covariance[OF valid src dst cov member])

lemmas time_covariance_preserves_native_membership = input_time_covariance_preserves_native_membership output_time_covariance_preserves_native_membership
end

ML \<open>
val roots = @{thms time_change_map_bijective time_change_relation_image time_change_preserves_zeroth
  native_time_covariance native_real_component_chart.time_change_preserves_native_zeroth
  native_real_component_chart.time_covariance_preserves_native_membership};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
