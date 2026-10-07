theory Native_Differential_Consequences
  imports "LCTR_Native_Family_Alignment.Native_Family_Alignment"
begin
context native_family_component_atlas
begin

definition ChosenRegular where "ChosenRegular rho = (SOME r. RegularAt rho r)"
definition ChosenTime where "ChosenTime Rel rho other alpha delta beta = (SOME cert.
  RepCertificate rho other alpha delta beta cert \<and>
  RepCovAt rho other alpha delta beta cert (Rel rho alpha beta) (Rel other delta beta))"
definition CovAt where "CovAt rho cert Rel = native_atlas_certificates.ValueCov k
  (TT rho) ProductSource ProductCoordinate cert Rel"

lemma chosen_regular:
  assumes h: "Complete Rel" and rep: "rho\<in>Reps"
  shows "RegularAt rho (ChosenRegular rho)"
proof -
  have ex: "\<exists>r. RegularAt rho r" using h rep
    by (auto simp: Complete_def C1_def AtlasAt_def)
  show ?thesis unfolding ChosenRegular_def by (rule someI_ex[OF ex])
qed

lemma native_smooth:
  "Complete Rel \<Longrightarrow> rho\<in>Reps \<Longrightarrow> Diff2 rho alpha beta gamma"
  by (auto simp: Complete_def C2_def JetAt_def)

lemma native_generated_jet_membership:
  "Complete Rel \<Longrightarrow> rho\<in>Reps \<Longrightarrow> theta\<in>Numeric rho alpha beta gamma \<Longrightarrow>
    Pair rho alpha beta gamma theta\<in>Rel rho alpha (beta,gamma)"
  by (auto simp: Complete_def C3_def MemberAt_def)

lemma native_flat_jet_membership:
  "Complete Rel \<Longrightarrow> rho\<in>Reps \<Longrightarrow> theta\<in>Numeric rho alpha beta gamma \<Longrightarrow>
    flat (Pair rho alpha beta gamma theta)\<in>image flat (Rel rho alpha (beta,gamma))"
  by (rule imageI; rule native_generated_jet_membership)

lemma native_zeroth_values:
  "rho\<in>Reps \<Longrightarrow> t\<in>Joint rho alpha beta gamma \<Longrightarrow>
    snd (Pair rho alpha beta gamma (tc rho alpha t)) 0 =
    (ic beta (input_value (component_at rho a) t), oc gamma (output_value (component_at rho a) t))"
  by (rule zeroth_pair_is_generated_law)

lemma chosen_value_covariance:
  assumes h: "Complete Rel" and rep: "rho\<in>Reps"
  shows "CovAt rho (ChosenRegular rho) (Rel rho)"
proof -
  interpret prod: native_product_atlas k "TT rho" "TD rho" "tc rho" IT ID ic OT OD oc
    by (rule actual_product_atlas[OF rep])
  have reg0: "RegularAt rho (ChosenRegular rho)" by (rule chosen_regular[OF h rep])
  have val0: "ValueAt rho (Rel rho)" using h rep by (auto simp: Complete_def C4_def)
  have reg: "prod.product.regular (ChosenRegular rho)" using reg0
    by (simp only: RegularAt_def ProductTarget_def[abs_def] ProductSource_def[abs_def] ProductCoordinate_def[abs_def])
  have val: "prod.product.Diff4 (Rel rho)" using val0
    by (simp only: ValueAt_def ProductTarget_def[abs_def] ProductSource_def[abs_def] ProductCoordinate_def[abs_def])
  have "prod.product.ValueCov (ChosenRegular rho) (Rel rho)"
    by (rule iffD1[OF prod.product.diff4_restricts[OF reg] val])
  then show ?thesis
    by (simp only: CovAt_def ProductTarget_def[abs_def] ProductSource_def[abs_def] ProductCoordinate_def[abs_def])
qed

lemma chosen_time_certificate:
  assumes h: "Complete Rel" and r: "rho\<in>Reps" and s: "other\<in>Reps"
  shows "RepCertificate rho other alpha delta beta (ChosenTime Rel rho other alpha delta beta) \<and>
    RepCovAt rho other alpha delta beta (ChosenTime Rel rho other alpha delta beta)
      (Rel rho alpha beta) (Rel other delta beta)"
proof -
  have time: "TimeAt rho other (Rel rho) (Rel other)"
    using h r s by (auto simp: Complete_def C5_def)
  have ex: "\<exists>cert. RepCertificate rho other alpha delta beta cert \<and>
    RepCovAt rho other alpha delta beta cert (Rel rho alpha beta) (Rel other delta beta)"
    using time unfolding TimeAt_def by blast
  show ?thesis unfolding ChosenTime_def by (rule someI_ex[OF ex])
qed

lemma native_time_relation_image:
  assumes h: "Complete Rel" and r: "rho\<in>Reps" and s: "other\<in>Reps"
  shows "image (certificate_map (ChosenTime Rel rho other alpha delta beta))
    (Rel rho alpha beta \<inter> (RepSourceNumeric rho other alpha delta \<times> jet_domain k (ProductTarget beta))) =
    Rel other delta beta \<inter> (RepTargetNumeric rho other alpha delta \<times> jet_domain k (ProductTarget beta))"
proof -
  have cert: "RepCertificate rho other alpha delta beta (ChosenTime Rel rho other alpha delta beta)" and
    cov: "RepCovAt rho other alpha delta beta (ChosenTime Rel rho other alpha delta beta)
      (Rel rho alpha beta) (Rel other delta beta)"
    using chosen_time_certificate[OF h r s, of alpha delta beta] by auto
  show ?thesis by (rule rep_relation_image[OF cert cov])
qed

lemma time_change_zeroth_value:
  assumes h: "Complete Rel" and r: "rho\<in>Reps" and s: "other\<in>Reps"
    and p: "p\<in>RepSourceNumeric rho other alpha delta \<times> jet_domain k (ProductTarget beta)"
  shows "snd (certificate_map (ChosenTime Rel rho other alpha delta beta) p) 0 = snd p 0"
proof -
  let ?cert = "ChosenTime Rel rho other alpha delta beta"
  have cert: "RepCertificate rho other alpha delta beta ?cert"
    using chosen_time_certificate[OF h r s, of alpha delta beta] by simp
  have at: "fst p\<in>RepSourceNumeric rho other alpha delta" and jet: "snd p\<in>jet_domain k (ProductTarget beta)"
    using p by auto
  have act: "time_acts k (fst p) (cert_forward ?cert (fst p)) (ProductTarget beta)
    (cert_backward ?cert) (cert_lift ?cert (fst p))"
    using cert at unfolding RepCertificate_def valid_time_certificate_def by blast
  obtain curve where curve: "curve_ck_at k (fst p) curve" "curve (fst p)\<in>ProductTarget beta"
    "jet k (fst p) curve = snd p" by (rule jet_domain_realization[OF jet])
  have application: "cert_lift ?cert (fst p) (snd p) =
    jet k (cert_forward ?cert (fst p)) (curve \<circ> cert_backward ?cert)"
    using time_acts_apply[OF act curve(1,2)] curve(3) by simp
  have inv: "cert_backward ?cert (cert_forward ?cert (fst p)) = fst p"
    using act by (simp add: time_acts_def)
  have zero: "jet k (fst p) curve 0 = snd p 0" using curve(3) by simp
  show ?thesis using application inv zero
    by (simp add: certificate_map_def jet_def restrict_def)
qed

lemma native_component_synthesis:
  assumes h: "Complete Rel"
  shows "(\<forall>rho\<in>Reps. RegularAt rho (ChosenRegular rho)) \<and>
    (\<forall>rho\<in>Reps. \<forall>alpha beta gamma. \<forall>theta\<in>Numeric rho alpha beta gamma.
      Pair rho alpha beta gamma theta\<in>Rel rho alpha (beta,gamma)) \<and>
    (\<forall>rho\<in>Reps. CovAt rho (ChosenRegular rho) (Rel rho)) \<and>
    (\<forall>rho\<in>Reps. \<forall>other\<in>Reps. TimeAt rho other (Rel rho) (Rel other))"
proof -
  have one: "\<forall>rho\<in>Reps. RegularAt rho (ChosenRegular rho)" by (intro ballI; rule chosen_regular[OF h])
  have two: "\<forall>rho\<in>Reps. \<forall>alpha beta gamma. \<forall>theta\<in>Numeric rho alpha beta gamma.
    Pair rho alpha beta gamma theta\<in>Rel rho alpha (beta,gamma)"
    by (intro ballI allI; rule native_generated_jet_membership[OF h]; assumption)
  have three: "\<forall>rho\<in>Reps. CovAt rho (ChosenRegular rho) (Rel rho)"
    by (intro ballI; rule chosen_value_covariance[OF h])
  have four: "\<forall>rho\<in>Reps. \<forall>other\<in>Reps. TimeAt rho other (Rel rho) (Rel other)"
    using h by (simp add: Complete_def C5_def)
  show ?thesis using one two three four by blast
qed
end

ML \<open>
val roots = @{thms native_family_component_atlas.chosen_regular
  native_family_component_atlas.native_smooth native_family_component_atlas.native_generated_jet_membership
  native_family_component_atlas.native_flat_jet_membership native_family_component_atlas.native_zeroth_values
  native_family_component_atlas.chosen_value_covariance native_family_component_atlas.chosen_time_certificate
  native_family_component_atlas.native_time_relation_image native_family_component_atlas.time_change_zeroth_value
  native_family_component_atlas.native_component_synthesis};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
