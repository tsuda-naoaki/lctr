theory Core_Native_Joint_Jets
  imports "LCTR_Core_Transported_Native_Jets.Core_Transported_Native_Jets"
    "LCTR_Core_Native_Law_Transport.Core_Native_Law_Transport"
begin

definition joint_extension where "joint_extension di do = (\<lambda>theta. (di theta,do theta))"
definition joint_jet where "joint_jet k theta di do = jet k theta (joint_extension di do)"
definition joint_generated_pair where "joint_generated_pair k di do theta = (theta,joint_jet k theta di do)"

lemma curve_ck_pair:
  assumes f: "curve_ck_at k a f" and g: "curve_ck_at k a g"
  shows "curve_ck_at k a (\<lambda>x. (f x,g x))"
proof -
  obtain S where S: "open S" "a\<in>S" "higher_differentiable_on S f k"
    using f unfolding curve_ck_at_def by blast
  obtain T where T: "open T" "a\<in>T" "higher_differentiable_on T g k"
    using g unfolding curve_ck_at_def by blast
  have F: "higher_differentiable_on (S\<inter>T) f k"
    by (rule higher_differentiable_on_subset[OF S(3)]) auto
  have G: "higher_differentiable_on (S\<inter>T) g k"
    by (rule higher_differentiable_on_subset[OF T(3)]) auto
  have O: "open (S\<inter>T)" using S T by auto
  have H: "higher_differentiable_on (S\<inter>T) (\<lambda>x. (f x,g x)) k"
    by (rule higher_differentiable_on_Pair[OF O F G])
  show ?thesis using O H S(2) T(2) unfolding curve_ck_at_def by blast
qed

locale joint_atlas_realizations = coordinate_atlas E Charts TD TT ID IT OD OT tc ic oc fin fout
  for E :: "'t set" and Charts :: "'i set"
    and TD :: "'i\<Rightarrow>'t set" and TT :: "'i\<Rightarrow>real set"
    and ID :: "'i\<Rightarrow>'vin set" and IT :: "'i\<Rightarrow>'nin::real_normed_vector set"
    and OD :: "'i\<Rightarrow>'vout set" and OT :: "'i\<Rightarrow>'nout::real_normed_vector set"
    and tc :: "'i\<Rightarrow>'t\<Rightarrow>real"
    and ic :: "'i\<Rightarrow>'vin\<Rightarrow>'nin" and oc :: "'i\<Rightarrow>'vout\<Rightarrow>'nout"
    and fin :: "'t\<Rightarrow>'vin" and fout :: "'t\<Rightarrow>'vout" +
  fixes i :: 'i and k :: nat and di :: "real\<Rightarrow>'nin" and do :: "real\<Rightarrow>'nout"
  assumes chosen: "i\<in>Charts"
    and data_in: "atlas_jet_data (numeric i) (fst \<circ> curve i) k di"
    and data_out: "atlas_jet_data (numeric i) (snd \<circ> curve i) k do"
begin
lemma joint_extension_agrees:
  "theta\<in>numeric i \<Longrightarrow> joint_extension di do theta=curve i theta"
  using data_in data_out by (auto simp: atlas_jet_data_def joint_extension_def)

lemma joint_extension_smooth:
  assumes theta: "theta\<in>numeric i"
  shows "curve_ck_at k theta (joint_extension di do)"
proof -
  have I: "curve_ck_at k theta di" and O: "curve_ck_at k theta do"
    using data_in data_out theta by (auto simp: atlas_jet_data_def)
  show ?thesis using curve_ck_pair[OF I O] by (simp add: joint_extension_def)
qed

lemma joint_extension_in_region:
  "theta\<in>numeric i \<Longrightarrow> joint_extension di do theta\<in>IT i\<times>OT i"
  using curve_values_typed[OF chosen] joint_extension_agrees by simp

lemma joint_zeroth_is_generated:
  "theta\<in>numeric i \<Longrightarrow> joint_jet k theta di do 0=curve i theta"
  using joint_extension_agrees by (simp add: joint_jet_def jet_def restrict_def)

lemma generated_pair_typed:
  assumes theta: "theta\<in>numeric i"
  shows "joint_generated_pair k di do theta\<in>TT i\<times>jet_domain k (IT i\<times>OT i)"
proof -
  have t: "theta\<in>TT i" using inverse_agrees_with_time_chart[OF chosen theta] by blast
  have j: "jet k theta (joint_extension di do)\<in>jet_domain k (IT i\<times>OT i)"
    by (rule jet_in_domain[where f="joint_extension di do" and a=theta, OF joint_extension_in_region[OF theta]])
  show ?thesis using t j by (simp add: joint_generated_pair_def joint_jet_def)
qed

lemma relation_membership_exact:
  "joint_generated_pair k di do ` numeric i\<subseteq>Rel \<longleftrightarrow>
    (\<forall>theta\<in>numeric i. joint_generated_pair k di do theta\<in>Rel)"
  by blast

lemma joint_realizations_agree_nearby:
  assumes otherI: "atlas_jet_data (numeric i) (fst \<circ> curve i) k ei"
    and otherO: "atlas_jet_data (numeric i) (snd \<circ> curve i) k eo"
    and opened: "open (numeric i)" and theta: "theta\<in>numeric i"
  shows "eventually (\<lambda>z. joint_extension di do z = joint_extension ei eo z) (nhds theta)"
proof -
  have e: "eventually (\<lambda>z. z\<in>numeric i) (nhds theta)"
    by (rule eventually_nhds_in_open[OF opened theta])
  show ?thesis using e
    by eventually_elim (use otherI otherO data_in data_out in \<open>auto simp: atlas_jet_data_def joint_extension_def\<close>)
qed

lemma joint_jet_independent_of_realizations:
  assumes "atlas_jet_data (numeric i) (fst \<circ> curve i) k ei"
    and "atlas_jet_data (numeric i) (snd \<circ> curve i) k eo"
    and "open (numeric i)" and "theta\<in>numeric i"
  shows "joint_jet k theta di do = joint_jet k theta ei eo"
  unfolding joint_jet_def
  by (rule jet_germ[OF joint_realizations_agree_nearby[OF assms]])
end

lemma pushed_joint_extension:
  "joint_extension (pushed_extension di) (pushed_extension do) = joint_extension di do"
  by (simp add: pushed_extension_def)
lemma pushed_joint_jet:
  "joint_jet k theta (pushed_extension di) (pushed_extension do) = joint_jet k (source_theta theta) di do"
  by (simp add: pushed_extension_def source_theta_def)
lemma pushed_generated_pair:
  "joint_generated_pair k (pushed_extension di) (pushed_extension do) theta =
    joint_generated_pair k di do (source_theta theta)"
  by (simp add: pushed_extension_def source_theta_def)

context real_transported_atlas
begin
lemma pushed_relation_membership:
  assumes i: "i\<in>Charts" and member: "\<And>theta. theta\<in>original.numeric i \<Longrightarrow> joint_generated_pair k di do theta\<in>Rel"
  shows "\<forall>theta\<in>pushed.numeric i. joint_generated_pair k (pushed_extension di) (pushed_extension do) theta\<in>Rel"
  using member numeric_domain_preserved[OF i] by (simp add: pushed_extension_def)
end

context native_real_component_chart
begin
lemma joint_zeroth_native_values:
  assumes i: "i\<in>Charts" and t: "t\<in>chart.joint i"
    and di: "atlas_jet_data (chart.numeric i) (fst \<circ> chart.curve i) k di"
    and do: "atlas_jet_data (chart.numeric i) (snd \<circ> chart.curve i) k do"
  shows "input_value (generated a) t\<in>ID i \<and> output_value (generated a) t\<in>OD i \<and>
    joint_jet k (tc i t) di do 0 = (ic i (input_value (generated a) t),oc i (output_value (generated a) t))"
proof -
  interpret joint: joint_atlas_realizations "evaluation_times a" Charts TD TT ID IT OD OT tc ic oc
    "input_value (generated a)" "output_value (generated a)" i k di do
    by (unfold_locales; use atlas i di do in \<open>auto simp: coordinate_atlas_def\<close>)
  have theta: "tc i t\<in>chart.numeric i" using t by (auto simp: chart.numeric_def)
  show ?thesis using native_side_curve[OF i t] joint.joint_zeroth_is_generated[OF theta] by (auto simp: prod_eq_iff)
qed

lemma joint_jets_all_time_embeddings:
  assumes newer: "observer_real C D B R Bind source_order rho1" and i: "i\<in>Charts"
    and di: "atlas_jet_data (chart.numeric i) (fst \<circ> chart.curve i) k di"
    and do: "atlas_jet_data (chart.numeric i) (snd \<circ> chart.curve i) k do"
  shows "\<exists>U f g. carrier_bijection (evaluation_times a) U f g \<and>
    (\<forall>q\<in>{q\<in>order_domain. rho q\<in>evaluation_times a}. f (rho q)=rho1 q) \<and>
    (\<forall>theta\<in>chart.numeric i.
      joint_generated_pair k (pushed_extension di) (pushed_extension do) theta = joint_generated_pair k di do (source_theta theta) \<and>
      joint_extension di do theta = pushed_curve chart.joint tc ic oc
        (input_value (generated a)) (output_value (generated a)) f g i theta)"
proof -
  have within: "evaluation_times a\<subseteq>real_domain" using component by (simp add: component_input_typed_def)
  interpret time: native_time_transport C D B R Bind source_order rho rho1 "evaluation_times a"
    by (unfold_locales; use newer within in \<open>auto simp: observer_real_def observer_real_axioms_def\<close>)
  have bij: "carrier_bijection (evaluation_times a) time.new_time time.change time.change_inverse"
    by (rule time.time.carrier_bijection_axioms)
  have ag: "joint_extension di do theta = pushed_curve chart.joint tc ic oc
      (input_value (generated a)) (output_value (generated a)) time.change time.change_inverse i theta"
    if theta: "theta\<in>chart.numeric i" for theta
    using native_law_reindex_jet_exact(2)[OF bij i di theta]
      native_law_reindex_jet_exact(2)[OF bij i do theta]
    by (simp add: joint_extension_def pushed_extension_def)
  show ?thesis
    by (rule exI[where x=time.new_time], rule exI[where x=time.change], rule exI[where x=time.change_inverse])
      (use bij time.change_commutes ag in \<open>auto simp: time.part_def pushed_generated_pair\<close>)
qed
end

ML \<open>
val roots = @{thms joint_atlas_realizations.joint_extension_agrees joint_atlas_realizations.joint_extension_smooth
  joint_atlas_realizations.joint_extension_in_region joint_atlas_realizations.joint_zeroth_is_generated
  joint_atlas_realizations.relation_membership_exact joint_atlas_realizations.joint_realizations_agree_nearby
  joint_atlas_realizations.joint_jet_independent_of_realizations pushed_joint_extension pushed_joint_jet
  pushed_generated_pair real_transported_atlas.pushed_relation_membership
  native_real_component_chart.joint_zeroth_native_values native_real_component_chart.joint_jets_all_time_embeddings};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
