theory Native_Family_Fibre_Conditions
  imports "LCTR_Native_Family_Certificate_Transport.Native_Family_Certificate_Transport"
begin
context native_family_fibre_atlas
begin

definition pull_relation where
  "pull_relation rho Rel u beta = Rel (indices.select_index rho u) beta"

lemma selected_joint:
  "rho\<in>Reps \<Longrightarrow> total.Joint rho (indices.select_index rho u) beta gamma = total.Joint rho u beta gamma"
  by (simp add: total.Joint_def total_domain_def selector_idempotent)
lemma selected_numeric:
  "rho\<in>Reps \<Longrightarrow> total.Numeric rho (indices.select_index rho u) beta gamma = total.Numeric rho u beta gamma"
  by (simp add: total.Numeric_def selected_joint total_coordinate_def selector_idempotent)
lemma selected_curve:
  assumes rep: "rho\<in>Reps"
  shows "total.Curve rho (indices.select_index rho u) beta gamma = total.Curve rho u beta gamma"
  by (rule ext) (simp add: total.Curve_def selected_joint[OF rep] total_coordinate_def selector_idempotent[OF rep])
lemma selected_diff2:
  "rho\<in>Reps \<Longrightarrow> total.Diff2 rho (indices.select_index rho u) beta gamma = total.Diff2 rho u beta gamma"
  by (simp add: total.Diff2_def selected_numeric selected_curve)
lemma selected_diff3:
  "rho\<in>Reps \<Longrightarrow> total.Diff3 rho (indices.select_index rho u) beta gamma Rel = total.Diff3 rho u beta gamma Rel"
  by (simp add: total.Diff3_def selected_numeric selected_curve)

lemma jet_fibre_exact:
  assumes rep: "rho\<in>Reps"
  shows "total.JetAt rho \<longleftrightarrow> (\<forall>alpha\<in>Fib rho. \<forall>beta gamma. total.Diff2 rho alpha beta gamma)"
proof
  assume "total.JetAt rho"
  then show "\<forall>alpha\<in>Fib rho. \<forall>beta gamma. total.Diff2 rho alpha beta gamma"
    by (simp add: total.JetAt_def)
next
  assume h: "\<forall>alpha\<in>Fib rho. \<forall>beta gamma. total.Diff2 rho alpha beta gamma"
  have "total.Diff2 rho u beta gamma" for u beta gamma
  proof -
    have at: "indices.select_index rho u\<in>Fib rho" by (rule indices.select_in[OF rep])
    have "total.Diff2 rho (indices.select_index rho u) beta gamma" using h at by blast
    then show ?thesis by (simp only: selected_diff2[OF rep])
  qed
  then show "total.JetAt rho" by (simp add: total.JetAt_def)
qed

lemma member_fibre_exact:
  assumes rep: "rho\<in>Reps"
  shows "total.JetAt rho \<and> total.MemberAt rho (pull_relation rho Rel) \<longleftrightarrow>
    (\<forall>alpha\<in>Fib rho. \<forall>beta gamma. total.Diff3 rho alpha beta gamma (Rel alpha (beta,gamma)))"
proof -
  have point: "total.Diff3 rho u beta gamma (pull_relation rho Rel u (beta,gamma)) =
    total.Diff3 rho (indices.select_index rho u) beta gamma (Rel (indices.select_index rho u) (beta,gamma))"
    for u beta gamma
    by (simp add: pull_relation_def selected_diff3[OF rep])
  show ?thesis
    by (simp only: total.third_at_actual point; rule sym; rule indices.forall_exact[OF rep])
qed

lemma selected_rep_certificate:
  assumes r: "rho\<in>Reps" and s: "other\<in>Reps"
  shows "total.RepCertificate rho other (indices.select_index rho u) (indices.select_index other v) beta cert =
    total.RepCertificate rho other u v beta cert"
  by (simp add: total.RepCertificate_def total.RepSourceNumeric_def total.RepTargetNumeric_def
    total.RepSource_def total.RepTarget_def total.RepForward_def total.RepBackward_def
    total_domain_def total_coordinate_def selector_idempotent[OF r] selector_idempotent[OF s])

lemma selected_rep_covariance:
  assumes r: "rho\<in>Reps" and s: "other\<in>Reps"
  shows "total.RepCovAt rho other (indices.select_index rho u) (indices.select_index other v) beta cert Rel S =
    total.RepCovAt rho other u v beta cert Rel S"
  by (simp add: total.RepCovAt_def total.RepSourceNumeric_def total.RepSource_def
    total_domain_def total_coordinate_def selector_idempotent[OF r] selector_idempotent[OF s])

lemma time_fibre_exact:
  assumes r: "rho\<in>Reps" and s: "other\<in>Reps"
  shows "total.TimeAt rho other (pull_relation rho Rel) (pull_relation other S) \<longleftrightarrow>
    (\<forall>alpha\<in>Fib rho. \<forall>delta\<in>Fib other. \<forall>beta. \<exists>cert.
      total.RepCertificate rho other alpha delta beta cert \<and>
      total.RepCovAt rho other alpha delta beta cert (Rel alpha beta) (S delta beta))"
proof -
  have point: "(total.RepCertificate rho other u v beta cert \<and>
    total.RepCovAt rho other u v beta cert
      (pull_relation rho Rel u beta) (pull_relation other S v beta)) =
    (total.RepCertificate rho other (indices.select_index rho u) (indices.select_index other v) beta cert \<and>
     total.RepCovAt rho other (indices.select_index rho u) (indices.select_index other v) beta cert
       (Rel (indices.select_index rho u) beta) (S (indices.select_index other v) beta))"
    for u v beta cert
    by (simp only: pull_relation_def selected_rep_certificate[OF r s] selected_rep_covariance[OF r s])
  show ?thesis
    by (simp only: total.TimeAt_def point; rule sym; rule indices.two_indices_exact[OF r s])
qed

context
  fixes rho :: "'c set set \<Rightarrow> real"
  assumes rep: "rho\<in>Reps"
begin
interpretation fibre: reindexed_atlas_certificates k "total_target rho" "total_domain rho" "total_coordinate rho"
  "\<lambda>b. IT (fst b)\<times>OT (snd b)" "\<lambda>b. ID (fst b)\<times>OD (snd b)"
  "\<lambda>b. map_prod (ic (fst b)) (oc (snd b))" "indices.select_index rho"
  by (rule actual_reindexed_certificate_instance[OF rep])

lemma fixed_fibre_exact: "fibre.Fixed = Fib rho"
  by (simp only: fibre.Fixed_def selected_fixed_is_original_fibre[OF rep])

lemma atlas_fibre_exact:
  "total.AtlasAt rho \<longleftrightarrow> (\<exists>r. fibre.RestrictedRegular r)"
  by (simp only: total.atlas_at_actual[OF rep] total.ProductTarget_def[abs_def]
    total.ProductSource_def[abs_def] total.ProductCoordinate_def[abs_def] fibre.regular_exists_exact)

lemma value_fibre_exact:
  "total.ValueAt rho (pull_relation rho Rel) \<longleftrightarrow>
    (\<exists>r. fibre.RestrictedRegular r \<and> fibre.RestrictedValueCov r Rel)"
proof -
  have eq: "pull_relation rho Rel = fibre.PullRelation Rel"
    by (rule ext; rule ext; simp only: pull_relation_def fibre.PullRelation_def)
  show ?thesis
    by (simp only: total.ValueAt_def total.ProductTarget_def[abs_def]
      total.ProductSource_def[abs_def] total.ProductCoordinate_def[abs_def] eq fibre.value_exists_exact)
qed
end
end

ML \<open>
val roots = @{thms native_family_fibre_atlas.selected_joint native_family_fibre_atlas.selected_numeric
  native_family_fibre_atlas.selected_curve native_family_fibre_atlas.selected_diff2
  native_family_fibre_atlas.selected_diff3 native_family_fibre_atlas.jet_fibre_exact
  native_family_fibre_atlas.member_fibre_exact native_family_fibre_atlas.selected_rep_certificate
  native_family_fibre_atlas.selected_rep_covariance native_family_fibre_atlas.time_fibre_exact
  native_family_fibre_atlas.fixed_fibre_exact native_family_fibre_atlas.atlas_fibre_exact
  native_family_fibre_atlas.value_fibre_exact};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
