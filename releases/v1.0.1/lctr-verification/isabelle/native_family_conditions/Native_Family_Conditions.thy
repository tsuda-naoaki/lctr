theory Native_Family_Conditions
  imports "LCTR_Native_Family_Charts.Native_Family_Charts"
begin

context native_family_component_atlas
begin
definition ProductTarget where "ProductTarget beta = IT (fst beta) \<times> OT (snd beta)"
definition ProductSource where "ProductSource beta = ID (fst beta) \<times> OD (snd beta)"
definition ProductCoordinate where "ProductCoordinate beta = map_prod (ic (fst beta)) (oc (snd beta))"
definition RegularAt where
  "RegularAt rho cert \<longleftrightarrow> native_atlas_certificates.regular k
    (TT rho) (TD rho) (tc rho) ProductTarget ProductSource ProductCoordinate cert"
definition AtlasAt where "AtlasAt rho \<longleftrightarrow> (\<exists>cert. RegularAt rho cert)"
definition ValueAt where
  "ValueAt rho Rel \<longleftrightarrow> native_atlas_certificates.Diff4 k
    (TT rho) (TD rho) (tc rho) ProductTarget ProductSource ProductCoordinate Rel"
definition JetAt where "JetAt rho \<longleftrightarrow> (\<forall>alpha beta gamma. Diff2 rho alpha beta gamma)"
definition MemberAt where
  "MemberAt rho Rel \<longleftrightarrow> (\<forall>alpha beta gamma. \<forall>theta\<in>Numeric rho alpha beta gamma.
    Pair rho alpha beta gamma theta\<in>Rel alpha (beta,gamma))"

definition RepSource where
  "RepSource rho other alpha delta = {t\<in>TD rho alpha. between rho other t\<in>TD other delta}"
definition RepTarget where
  "RepTarget rho other alpha delta = {u\<in>TD other delta.
    inv_into (eval_at rho a) (between rho other) u\<in>TD rho alpha}"
definition RepSourceNumeric where
  "RepSourceNumeric rho other alpha delta = image (tc rho alpha) (RepSource rho other alpha delta)"
definition RepTargetNumeric where
  "RepTargetNumeric rho other alpha delta = image (tc other delta) (RepTarget rho other alpha delta)"
definition RepForward where
  "RepForward rho other alpha delta theta =
    tc other delta (between rho other (inv_into (RepSource rho other alpha delta) (tc rho alpha) theta))"
definition RepBackward where
  "RepBackward rho other alpha delta theta =
    tc rho alpha (inv_into (eval_at rho a) (between rho other)
      (inv_into (RepTarget rho other alpha delta) (tc other delta) theta))"
definition RepCertificate :: "('c set set \<Rightarrow> real) \<Rightarrow> ('c set set \<Rightarrow> real) \<Rightarrow>
    'ti \<Rightarrow> 'ti \<Rightarrow> ('bi \<times> 'bo) \<Rightarrow> ('e \<times> 'f) time_change_certificate \<Rightarrow> bool" where
  "RepCertificate rho other alpha delta beta cert \<longleftrightarrow>
    valid_time_certificate k (ProductTarget beta)
      (RepSourceNumeric rho other alpha delta) (RepTargetNumeric rho other alpha delta) cert \<and>
    (\<forall>theta\<in>RepSourceNumeric rho other alpha delta.
      cert_forward cert theta = RepForward rho other alpha delta theta) \<and>
    (\<forall>theta\<in>RepTargetNumeric rho other alpha delta.
      cert_backward cert theta = RepBackward rho other alpha delta theta)"
definition RepCovAt :: "('c set set \<Rightarrow> real) \<Rightarrow> ('c set set \<Rightarrow> real) \<Rightarrow>
    'ti \<Rightarrow> 'ti \<Rightarrow> ('bi \<times> 'bo) \<Rightarrow> ('e \<times> 'f) time_change_certificate \<Rightarrow>
    (real \<times> (nat \<Rightarrow> 'e \<times> 'f)) set \<Rightarrow>
    (real \<times> (nat \<Rightarrow> 'e \<times> 'f)) set \<Rightarrow> bool" where
  "RepCovAt rho other alpha delta beta cert RelSource RelTarget \<longleftrightarrow>
    (\<forall>p\<in>RepSourceNumeric rho other alpha delta \<times> jet_domain k (ProductTarget beta).
      p\<in>RelSource \<longleftrightarrow> certificate_map cert p\<in>RelTarget)"
definition TimeAt where
  "TimeAt rho other RelSource RelTarget \<longleftrightarrow>
    (\<forall>alpha delta beta. \<exists>cert. RepCertificate rho other alpha delta beta cert \<and>
      RepCovAt rho other alpha delta beta cert (RelSource alpha beta) (RelTarget delta beta))"

lemma atlas_at_actual:
  assumes rep: "rho\<in>Reps"
  shows "AtlasAt rho \<longleftrightarrow> native_atlas_certificates.Diff1 k
    (TT rho) (TD rho) (tc rho) ProductTarget ProductSource ProductCoordinate"
proof -
  interpret prod: native_product_atlas k "TT rho" "TD rho" "tc rho" IT ID ic OT OD oc
    by (rule actual_product_atlas[OF rep])
  show ?thesis
    by (simp only: AtlasAt_def RegularAt_def ProductTarget_def[abs_def]
      ProductSource_def[abs_def] ProductCoordinate_def[abs_def] prod.product.Diff1_def)
qed

lemma third_at_actual:
  "JetAt rho \<and> MemberAt rho Rel \<longleftrightarrow>
    (\<forall>alpha beta gamma. Diff3 rho alpha beta gamma (Rel alpha (beta,gamma)))"
  by (auto simp: JetAt_def MemberAt_def third_condition_exact)

lemma fourth_at_actual:
  assumes rep: "rho\<in>Reps" and vcov: "ValueAt rho Rel"
  shows "AtlasAt rho"
proof -
  interpret prod: native_product_atlas k "TT rho" "TD rho" "tc rho" IT ID ic OT OD oc
    by (rule actual_product_atlas[OF rep])
  have "prod.product.Diff4 Rel" using vcov
    by (simp only: ValueAt_def ProductTarget_def[abs_def]
      ProductSource_def[abs_def] ProductCoordinate_def[abs_def])
  then have "prod.product.Diff1" by (rule prod.product.diff4_requires_diff1)
  then show ?thesis using atlas_at_actual[OF rep]
    by (simp only: ProductTarget_def[abs_def] ProductSource_def[abs_def] ProductCoordinate_def[abs_def])
qed

lemma rep_certificate_uses_actual_change:
  assumes rep: "RepCertificate rho other alpha delta beta cert"
    and source: "rho\<in>Reps"
    and t: "t\<in>RepSource rho other alpha delta"
  shows "cert_forward cert (tc rho alpha t) = tc other delta (between rho other t)"
proof -
  have inj: "inj_on (tc rho alpha) (TD rho alpha)"
    using time_charts[OF source] by (simp add: bij_betw_def)
  have sub: "RepSource rho other alpha delta\<subseteq>TD rho alpha" by (auto simp: RepSource_def)
  have rest: "inj_on (tc rho alpha) (RepSource rho other alpha delta)" by (rule inj_on_subset[OF inj sub])
  have inv: "inv_into (RepSource rho other alpha delta) (tc rho alpha) (tc rho alpha t) = t"
    by (rule inv_into_f_f[OF rest t])
  have dom: "tc rho alpha t\<in>RepSourceNumeric rho other alpha delta" using t by (auto simp: RepSourceNumeric_def)
  show ?thesis using rep dom by (simp add: RepCertificate_def RepForward_def inv)
qed

lemma rep_relation_image:
  assumes cert: "RepCertificate rho other alpha delta beta cert"
    and cov: "RepCovAt rho other alpha delta beta cert RelSource RelTarget"
  shows "image (certificate_map cert)
    (RelSource \<inter> (RepSourceNumeric rho other alpha delta \<times> jet_domain k (ProductTarget beta))) =
    RelTarget \<inter> (RepTargetNumeric rho other alpha delta \<times> jet_domain k (ProductTarget beta))"
proof -
  have valid: "valid_time_certificate k (ProductTarget beta)
    (RepSourceNumeric rho other alpha delta) (RepTargetNumeric rho other alpha delta) cert"
    using cert by (simp add: RepCertificate_def)
  have bij: "bij_betw (certificate_map cert)
    (RepSourceNumeric rho other alpha delta \<times> jet_domain k (ProductTarget beta))
    (RepTargetNumeric rho other alpha delta \<times> jet_domain k (ProductTarget beta))"
    by (rule certificate_bijection[OF valid])
  show ?thesis by (rule ambient_restriction_image[OF bij]) (use cov in \<open>simp add: RepCovAt_def\<close>)
qed

definition C1 where "C1 \<longleftrightarrow> (\<forall>rho\<in>Reps. AtlasAt rho)"
definition C2 where "C2 \<longleftrightarrow> (\<forall>rho\<in>Reps. JetAt rho)"
definition C3 where "C3 Rel \<longleftrightarrow> (\<forall>rho\<in>Reps. JetAt rho \<and> MemberAt rho (Rel rho))"
definition C4 where "C4 Rel \<longleftrightarrow> (\<forall>rho\<in>Reps. AtlasAt rho \<and> ValueAt rho (Rel rho))"
definition C5 where "C5 Rel \<longleftrightarrow> (\<forall>rho\<in>Reps. \<forall>other\<in>Reps.
  AtlasAt rho \<and> AtlasAt other \<and> TimeAt rho other (Rel rho) (Rel other))"
definition Complete where "Complete Rel \<longleftrightarrow> C1 \<and> C2 \<and> C3 Rel \<and> C4 Rel \<and> C5 Rel"
definition F1 where "F1 \<longleftrightarrow> \<not>C1"
definition F2 where "F2 \<longleftrightarrow> C1 \<and> \<not>C2"
definition F3 where "F3 Rel \<longleftrightarrow> C1 \<and> C2 \<and> \<not>C3 Rel"
definition F4 where "F4 Rel \<longleftrightarrow> C1 \<and> \<not>C4 Rel"
definition F5 where "F5 Rel \<longleftrightarrow> C1 \<and> \<not>C5 Rel"

lemma first_condition_exact: "C1 \<longleftrightarrow> (\<forall>rho\<in>Reps. \<exists>cert. RegularAt rho cert)"
  by (simp add: C1_def AtlasAt_def)
lemma second_condition_exact:
  "C2 \<longleftrightarrow> (\<forall>rho\<in>Reps. \<forall>alpha beta gamma. Diff2 rho alpha beta gamma)"
  by (simp add: C2_def JetAt_def)
lemma third_condition_all_representations:
  "C3 Rel \<longleftrightarrow> (\<forall>rho\<in>Reps. \<forall>alpha beta gamma.
    Diff3 rho alpha beta gamma (Rel rho alpha (beta,gamma)))"
  by (simp add: C3_def third_at_actual)
lemma fourth_condition_exact:
  "C4 Rel \<longleftrightarrow> (\<forall>rho\<in>Reps. ValueAt rho (Rel rho))"
  using fourth_at_actual by (auto simp: C4_def)
lemma fifth_condition_exact:
  "C5 Rel \<longleftrightarrow> (\<forall>rho\<in>Reps. \<forall>other\<in>Reps. AtlasAt rho \<and> AtlasAt other \<and>
    (\<forall>alpha delta beta. \<exists>cert. RepCertificate rho other alpha delta beta cert \<and>
      RepCovAt rho other alpha delta beta cert (Rel rho alpha beta) (Rel other delta beta)))"
  by (simp add: C5_def TimeAt_def)
lemma native_five_failure_cover:
  "\<not>Complete Rel \<longleftrightarrow> F1 \<or> F2 \<or> F3 Rel \<or> F4 Rel \<or> F5 Rel"
  by (auto simp: Complete_def F1_def F2_def F3_def F4_def F5_def)
end

ML \<open>
val roots = @{thms native_family_component_atlas.atlas_at_actual
  native_family_component_atlas.third_at_actual native_family_component_atlas.fourth_at_actual
  native_family_component_atlas.rep_certificate_uses_actual_change
  native_family_component_atlas.rep_relation_image
  native_family_component_atlas.first_condition_exact native_family_component_atlas.second_condition_exact
  native_family_component_atlas.third_condition_all_representations native_family_component_atlas.fourth_condition_exact
  native_family_component_atlas.fifth_condition_exact native_family_component_atlas.native_five_failure_cover};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
