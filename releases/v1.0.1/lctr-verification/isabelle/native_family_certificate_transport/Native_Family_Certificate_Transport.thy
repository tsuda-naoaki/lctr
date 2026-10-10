theory Native_Family_Certificate_Transport
  imports "LCTR_Native_Family_Index_Transport.Native_Family_Index_Transport"
begin

definition reindex_certificate :: "('a\<Rightarrow>'a) \<Rightarrow> ('a,'b,'e) atlas_certificate \<Rightarrow> ('a,'b,'e) atlas_certificate" where
  "reindex_certificate pick r = \<lparr>
    vforward = (\<lambda>a b c. vforward r (pick a) b c),
    vbackward = (\<lambda>a b c. vbackward r (pick a) b c),
    vlift = (\<lambda>a b c. vlift r (pick a) b c),
    vinverse = (\<lambda>a b c. vinverse r (pick a) b c),
    tforward = (\<lambda>a d b. tforward r (pick a) (pick d) b),
    tbackward = (\<lambda>a d b. tbackward r (pick a) (pick d) b),
    tlift = (\<lambda>a d b. tlift r (pick a) (pick d) b),
    tinverse = (\<lambda>a d b. tinverse r (pick a) (pick d) b)\<rparr>"

locale reindexed_atlas_certificates = native_atlas_certificates k TT TD tc VT VD vc
  for k :: nat and TT :: "'a\<Rightarrow>real set" and TD :: "'a\<Rightarrow>'t set"
    and tc :: "'a\<Rightarrow>'t\<Rightarrow>real"
    and VT :: "'b\<Rightarrow>'e::real_normed_vector set" and VD :: "'b\<Rightarrow>'v set"
    and vc :: "'b\<Rightarrow>'v\<Rightarrow>'e" +
  fixes pick :: "'a\<Rightarrow>'a"
  assumes idempotent: "\<And>a. pick (pick a) = pick a"
    and same_target: "\<And>a. TT (pick a) = TT a"
    and same_domain: "\<And>a. TD (pick a) = TD a"
    and same_coordinate: "\<And>a. tc (pick a) = tc a"
begin
definition Fixed where "Fixed = {a. pick a = a}"
definition RestrictedRegular where
  "RestrictedRegular r \<longleftrightarrow>
    (\<forall>a\<in>Fixed. \<forall>b c. value_bound r a b c) \<and>
    (\<forall>a\<in>Fixed. \<forall>d\<in>Fixed. \<forall>b. time_bound r a d b)"
definition PullRelation where "PullRelation Rel a b = Rel (pick a) b"
definition RestrictedValueCov where
  "RestrictedValueCov r Rel \<longleftrightarrow> (\<forall>a\<in>Fixed. \<forall>b c. \<forall>p\<in>VSpace a b c.
    p\<in>Rel a b \<longleftrightarrow> value_jet_map (vlift r a b c) p\<in>Rel a c)"

lemma picked_fixed: "pick a\<in>Fixed" by (simp add: Fixed_def idempotent)
lemma fixed_identity: "a\<in>Fixed \<Longrightarrow> pick a = a" by (simp add: Fixed_def)
lemma value_bound_reindexed:
  "value_bound (reindex_certificate pick r) a b c \<longleftrightarrow> value_bound r (pick a) b c"
  by (simp add: value_bound_def reindex_certificate_def same_target)
lemma time_bound_reindexed:
  "time_bound (reindex_certificate pick r) a d b \<longleftrightarrow> time_bound r (pick a) (pick d) b"
  by (simp add: time_bound_def reindex_certificate_def same_domain same_coordinate)
lemma value_space_reindexed: "VSpace (pick a) b c = VSpace a b c"
  by (simp add: VSpace_def same_target)

lemma regular_reindex:
  assumes rr: "RestrictedRegular r"
  shows "regular (reindex_certificate pick r)"
proof -
  have vb: "value_bound r (pick a) b c" for a b c
    using rr picked_fixed[of a] by (auto simp: RestrictedRegular_def)
  have tb: "time_bound r (pick a) (pick d) b" for a d b
    using rr picked_fixed[of a] picked_fixed[of d] by (auto simp: RestrictedRegular_def)
  show ?thesis using vb tb by (simp add: regular_def value_bound_reindexed time_bound_reindexed)
qed

lemma regular_restrict:
  "regular r \<Longrightarrow> RestrictedRegular r"
  by (auto simp: regular_def RestrictedRegular_def)

lemma regular_exists_exact:
  "Diff1 \<longleftrightarrow> (\<exists>r. RestrictedRegular r)"
proof
  assume "Diff1"
  then obtain r where "regular r" unfolding Diff1_def by blast
  then have "RestrictedRegular r" by (rule regular_restrict)
  then show "\<exists>r. RestrictedRegular r" by (rule exI)
next
  assume "\<exists>r. RestrictedRegular r"
  then obtain r where "RestrictedRegular r" by blast
  then have "regular (reindex_certificate pick r)" by (rule regular_reindex)
  then show "Diff1" unfolding Diff1_def by (rule exI)
qed

lemma value_cov_reindex:
  assumes rv: "RestrictedValueCov r Rel"
  shows "ValueCov (reindex_certificate pick r) (PullRelation Rel)"
proof -
  have body: "p\<in>Rel (pick a) b \<longleftrightarrow>
    value_jet_map (vlift r (pick a) b c) p\<in>Rel (pick a) c"
    if hp: "p\<in>VSpace a b c" for a b c p
    using rv picked_fixed[of a] hp
    by (auto simp: RestrictedValueCov_def value_space_reindexed)
  show ?thesis using body
    by (simp add: ValueCov_def PullRelation_def reindex_certificate_def)
qed

lemma value_cov_restrict:
  assumes cov: "ValueCov r (PullRelation Rel)"
  shows "RestrictedValueCov r Rel"
proof -
  have body: "p\<in>Rel a b \<longleftrightarrow> value_jet_map (vlift r a b c) p\<in>Rel a c"
    if fixed: "a\<in>Fixed" and hp: "p\<in>VSpace a b c" for a b c p
  proof -
    have point: "p\<in>PullRelation Rel a b \<longleftrightarrow>
      value_jet_map (vlift r a b c) p\<in>PullRelation Rel a c"
      using cov hp unfolding ValueCov_def by blast
    show ?thesis using point
      by (simp only: PullRelation_def fixed_identity[OF fixed])
  qed
  show ?thesis using body by (simp add: RestrictedValueCov_def)
qed

lemma value_exists_exact:
  "Diff4 (PullRelation Rel) \<longleftrightarrow> (\<exists>r. RestrictedRegular r \<and> RestrictedValueCov r Rel)"
proof
  assume "Diff4 (PullRelation Rel)"
  then obtain r where r: "regular r" "ValueCov r (PullRelation Rel)" unfolding Diff4_def by blast
  have "RestrictedRegular r" by (rule regular_restrict[OF r(1)])
  moreover have "RestrictedValueCov r Rel" by (rule value_cov_restrict[OF r(2)])
  ultimately show "\<exists>r. RestrictedRegular r \<and> RestrictedValueCov r Rel" by blast
next
  assume "\<exists>r. RestrictedRegular r \<and> RestrictedValueCov r Rel"
  then obtain r where r: "RestrictedRegular r" "RestrictedValueCov r Rel" by blast
  have "regular (reindex_certificate pick r)" by (rule regular_reindex[OF r(1)])
  moreover have "ValueCov (reindex_certificate pick r) (PullRelation Rel)"
    by (rule value_cov_reindex[OF r(2)])
  ultimately show "Diff4 (PullRelation Rel)" unfolding Diff4_def by blast
qed
end

context native_family_fibre_atlas
begin
lemma selector_idempotent:
  "rho\<in>Reps \<Longrightarrow> indices.select_index rho (indices.select_index rho u) = indices.select_index rho u"
  by (rule indices.select_fixed; rule indices.select_in)

lemma total_chart_selector_invariant:
  "rho\<in>Reps \<Longrightarrow>
    total_target rho (indices.select_index rho u) = total_target rho u \<and>
    total_domain rho (indices.select_index rho u) = total_domain rho u \<and>
    total_coordinate rho (indices.select_index rho u) = total_coordinate rho u"
  by (simp add: total_target_def total_domain_def total_coordinate_def selector_idempotent)

lemma actual_reindexed_certificate_instance:
  assumes rep: "rho\<in>Reps"
  shows "reindexed_atlas_certificates (total_target rho) (total_domain rho) (total_coordinate rho)
    (\<lambda>b. IT (fst b)\<times>OT (snd b)) (\<lambda>b. ID (fst b)\<times>OD (snd b))
    (\<lambda>b. map_prod (ic (fst b)) (oc (snd b))) (indices.select_index rho)"
proof -
  interpret prod: native_product_atlas k "total_target rho" "total_domain rho" "total_coordinate rho" IT ID ic OT OD oc
    by (rule actual_totalized_atlas[OF rep])
  show ?thesis
    by unfold_locales (use rep in \<open>simp_all add: selector_idempotent total_chart_selector_invariant\<close>)
qed

lemma selected_fixed_is_original_fibre:
  assumes rep: "rho\<in>Reps"
  shows "{u. indices.select_index rho u = u} = Fib rho"
proof (rule equalityI)
  show "{u. indices.select_index rho u = u} \<subseteq> Fib rho"
  proof
    fix u assume h: "u\<in>{u. indices.select_index rho u = u}"
    have "indices.select_index rho u\<in>Fib rho" by (rule indices.select_in[OF rep])
    then show "u\<in>Fib rho" using h by simp
  qed
  show "Fib rho \<subseteq> {u. indices.select_index rho u = u}"
    by (auto intro: indices.select_fixed)
qed
end

ML \<open>
val roots = @{thms reindexed_atlas_certificates.picked_fixed
  reindexed_atlas_certificates.fixed_identity reindexed_atlas_certificates.value_bound_reindexed
  reindexed_atlas_certificates.time_bound_reindexed reindexed_atlas_certificates.value_space_reindexed
  reindexed_atlas_certificates.regular_reindex reindexed_atlas_certificates.regular_restrict
  reindexed_atlas_certificates.regular_exists_exact reindexed_atlas_certificates.value_cov_reindex
  reindexed_atlas_certificates.value_cov_restrict reindexed_atlas_certificates.value_exists_exact
  native_family_fibre_atlas.selector_idempotent native_family_fibre_atlas.total_chart_selector_invariant
  native_family_fibre_atlas.actual_reindexed_certificate_instance
  native_family_fibre_atlas.selected_fixed_is_original_fibre};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
