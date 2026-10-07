theory Core_Transported_Native_Jets
  imports "LCTR_Core_Curve_Regularity.Core_Curve_Regularity"
    "LCTR_Core_Transported_Law_Charts.Core_Transported_Law_Charts"
begin

definition source_theta :: "'a \<Rightarrow> 'a" where "source_theta theta = theta"
definition pushed_extension :: "'a \<Rightarrow> 'a" where "pushed_extension d = d"
definition atlas_jet_data where
  "atlas_jet_data N q k d \<longleftrightarrow> (\<forall>theta\<in>N. d theta=q theta \<and> curve_ck_at k theta d)"
definition atlas_jet where "atlas_jet k theta d = jet k theta d"
definition native_jet where "native_jet k theta d = jet k theta d"

lemma source_theta_value: "source_theta theta = theta"
  by (simp add: source_theta_def)
lemma transported_extension_fixed: "pushed_extension d = d"
  by (simp add: pushed_extension_def)
lemma transported_jet_equal:
  "atlas_jet k theta (pushed_extension d) = atlas_jet k (source_theta theta) d"
  by (simp add: pushed_extension_def source_theta_def)
lemma native_jet_data_exact: "atlas_jet k theta d = native_jet k theta d"
  by (simp add: atlas_jet_def native_jet_def)

context transported_coordinate_atlas
begin
lemma curve_at_transported_coordinate:
  assumes i: "i\<in>Charts" and theta: "theta\<in>pushed.numeric i"
  shows "pushed.curve i theta = original.curve i (source_theta theta)"
proof -
  have n: "theta\<in>original.numeric i" using theta numeric_domain_preserved[OF i] by simp
  obtain t where t: "t\<in>original.joint i" "theta=tc i t"
    using n unfolding original.numeric_def by blast
  show ?thesis using native_curve_preserved[OF i t(1)] numeric_time_preserved[OF i t(1)] t(2)
    by (simp add: source_theta_def)
qed
end

locale real_transported_atlas = transported_coordinate_atlas E Charts TD TT ID IT OD OT tc ic oc fin fout U f g
  for E :: "'t set" and Charts :: "'i set"
    and TD :: "'i\<Rightarrow>'t set" and TT :: "'i\<Rightarrow>real set"
    and ID :: "'i\<Rightarrow>'vin set" and IT :: "'i\<Rightarrow>'nin::real_normed_vector set"
    and OD :: "'i\<Rightarrow>'vout set" and OT :: "'i\<Rightarrow>'nout::real_normed_vector set"
    and tc :: "'i\<Rightarrow>'t\<Rightarrow>real"
    and ic :: "'i\<Rightarrow>'vin\<Rightarrow>'nin" and oc :: "'i\<Rightarrow>'vout\<Rightarrow>'nout"
    and fin :: "'t\<Rightarrow>'vin" and fout :: "'t\<Rightarrow>'vout"
    and U :: "'u set" and f :: "'t\<Rightarrow>'u" and g :: "'u\<Rightarrow>'t"
begin
lemma push_jet_data:
  fixes side :: "'nin\<times>'nout \<Rightarrow> 'v::real_normed_vector"
  assumes i: "i\<in>Charts" and d: "atlas_jet_data (original.numeric i) (side \<circ> original.curve i) k d"
  shows "atlas_jet_data (pushed.numeric i) (side \<circ> pushed.curve i) k (pushed_extension d)"
  using d numeric_domain_preserved[OF i] curve_at_transported_coordinate[OF i]
  by (auto simp: atlas_jet_data_def pushed_extension_def source_theta_def)

lemma transported_regularity:
  fixes side :: "'nin\<times>'nout \<Rightarrow> 'v::real_normed_vector"
  assumes i: "i\<in>Charts" and d: "atlas_jet_data (original.numeric i) (side \<circ> original.curve i) k d"
    and theta: "theta\<in>pushed.numeric i"
  shows "curve_ck_at k theta (pushed_extension d)"
  using push_jet_data[OF i d] theta by (simp add: atlas_jet_data_def)

lemma realization_in_value_chart:
  assumes i: "i\<in>Charts" and theta: "theta\<in>original.numeric i"
  shows "(atlas_jet_data (original.numeric i) (fst \<circ> original.curve i) k di \<longrightarrow> di theta\<in>IT i) \<and>
    (atlas_jet_data (original.numeric i) (snd \<circ> original.curve i) k do \<longrightarrow> do theta\<in>OT i)"
  using original.curve_values_typed[OF i theta] theta
  by (auto simp: atlas_jet_data_def)

lemma input_realization_in_value_chart:
  assumes i: "i\<in>Charts" and theta: "theta\<in>original.numeric i"
    and d: "atlas_jet_data (original.numeric i) (fst \<circ> original.curve i) k d"
  shows "d theta\<in>IT i \<and> atlas_jet k theta d\<in>jet_domain k (IT i)"
proof -
  have h: "d theta\<in>IT i"
    using original.curve_values_typed[OF i theta] d theta by (auto simp: atlas_jet_data_def)
  show ?thesis using h jet_in_domain[where f=d and a=theta and k=k, OF h] by (simp add: atlas_jet_def)
qed

lemma output_realization_in_value_chart:
  assumes i: "i\<in>Charts" and theta: "theta\<in>original.numeric i"
    and d: "atlas_jet_data (original.numeric i) (snd \<circ> original.curve i) k d"
  shows "d theta\<in>OT i \<and> atlas_jet k theta d\<in>jet_domain k (OT i)"
proof -
  have h: "d theta\<in>OT i"
    using original.curve_values_typed[OF i theta] d theta by (auto simp: atlas_jet_data_def)
  show ?thesis using h jet_in_domain[where f=d and a=theta and k=k, OF h] by (simp add: atlas_jet_def)
qed

lemma transported_jet_membership:
  assumes i: "i\<in>Charts" and member: "\<And>theta. theta\<in>original.numeric i \<Longrightarrow> (theta,atlas_jet k theta d)\<in>Rel"
    and theta: "theta\<in>pushed.numeric i"
  shows "(source_theta theta,atlas_jet k theta (pushed_extension d))\<in>Rel"
  using member theta numeric_domain_preserved[OF i]
  by (simp add: source_theta_def pushed_extension_def)
end

locale native_real_component_chart = native_component_chart C D B R Bind source_order rho indices val_carriers observable
    a Charts TD TT ID IT OD OT tc ic oc
  for C :: "'c set" and D :: "'d set" and B :: "'b set"
    and R :: "('c\<times>'d\<times>'b)set"
    and Bind :: "(('c\<times>'d\<times>'b)\<times>('c\<times>'d\<times>'b))set"
    and source_order :: "('c\<times>'c)set" and rho :: "'c set set\<Rightarrow>real"
    and indices :: "'q set" and val_carriers :: "'q\<Rightarrow>'v set"
    and observable :: "'q\<Rightarrow>'b set\<Rightarrow>'v"
    and a :: "('q,'v) native_component_input" and Charts :: "'i set"
    and TD :: "'i\<Rightarrow>real set" and TT :: "'i\<Rightarrow>real set"
    and ID :: "'i\<Rightarrow>('q\<Rightarrow>'v)set" and IT :: "'i\<Rightarrow>'nin::real_normed_vector set"
    and OD :: "'i\<Rightarrow>('q\<Rightarrow>'v)set" and OT :: "'i\<Rightarrow>'nout::real_normed_vector set"
    and tc :: "'i\<Rightarrow>real\<Rightarrow>real"
    and ic :: "'i\<Rightarrow>('q\<Rightarrow>'v)\<Rightarrow>'nin"
    and oc :: "'i\<Rightarrow>('q\<Rightarrow>'v)\<Rightarrow>'nout"
begin
lemma native_law_reindex_jet_exact:
  fixes side :: "'nin\<times>'nout \<Rightarrow> 'w::real_normed_vector"
  assumes reindex: "carrier_bijection (evaluation_times a) U f g" and i: "i\<in>Charts"
    and d: "atlas_jet_data (chart.numeric i) (side \<circ> chart.curve i) k d"
    and theta: "theta\<in>chart.numeric i"
  shows "atlas_jet k theta (pushed_extension d) = native_jet k (source_theta theta) d"
    and "pushed_extension d theta = side (pushed_curve chart.joint tc ic oc
      (input_value (generated a)) (output_value (generated a)) f g i theta)"
    and "curve_ck_at k theta (pushed_extension d)"
proof -
  interpret tr: real_transported_atlas "evaluation_times a" Charts TD TT ID IT OD OT tc ic oc
    "input_value (generated a)" "output_value (generated a)" U f g
    by (unfold_locales; use atlas reindex in \<open>auto simp: coordinate_atlas_def carrier_bijection_def\<close>)
  have pt: "theta\<in>tr.pushed.numeric i" using theta tr.numeric_domain_preserved[OF i] by simp
  show "atlas_jet k theta (pushed_extension d) = native_jet k (source_theta theta) d"
    by (simp add: pushed_extension_def source_theta_def native_jet_data_exact)
  have agree: "pushed_extension d theta = side (tr.pushed.curve i theta)"
    using tr.push_jet_data[OF i d] pt by (simp add: atlas_jet_data_def)
  show "pushed_extension d theta = side (pushed_curve chart.joint tc ic oc
      (input_value (generated a)) (output_value (generated a)) f g i theta)"
    using agree tr.pushed_curve_formula[OF i] by simp
  show "curve_ck_at k theta (pushed_extension d)" by (rule tr.transported_regularity[OF i d pt])
qed
end

ML \<open>
val roots = @{thms source_theta_value transported_coordinate_atlas.curve_at_transported_coordinate
  transported_extension_fixed real_transported_atlas.transported_regularity
  real_transported_atlas.realization_in_value_chart transported_jet_equal
  real_transported_atlas.transported_jet_membership native_jet_data_exact
  native_real_component_chart.native_law_reindex_jet_exact};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
