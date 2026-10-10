theory Native_Atlas_Certificates
  imports "LCTR_Native_Value_Change.Native_Value_Change"
begin

record ('a,'b,'e) atlas_certificate =
  vforward :: "'a\<Rightarrow>'b\<Rightarrow>'b\<Rightarrow>'e\<Rightarrow>'e"
  vbackward :: "'a\<Rightarrow>'b\<Rightarrow>'b\<Rightarrow>'e\<Rightarrow>'e"
  vlift :: "'a\<Rightarrow>'b\<Rightarrow>'b\<Rightarrow>real\<Rightarrow>(nat\<Rightarrow>'e)\<Rightarrow>(nat\<Rightarrow>'e)"
  vinverse :: "'a\<Rightarrow>'b\<Rightarrow>'b\<Rightarrow>real\<Rightarrow>(nat\<Rightarrow>'e)\<Rightarrow>(nat\<Rightarrow>'e)"
  tforward :: "'a\<Rightarrow>'a\<Rightarrow>'b\<Rightarrow>real\<Rightarrow>real"
  tbackward :: "'a\<Rightarrow>'a\<Rightarrow>'b\<Rightarrow>real\<Rightarrow>real"
  tlift :: "'a\<Rightarrow>'a\<Rightarrow>'b\<Rightarrow>real\<Rightarrow>(nat\<Rightarrow>'e)\<Rightarrow>(nat\<Rightarrow>'e)"
  tinverse :: "'a\<Rightarrow>'a\<Rightarrow>'b\<Rightarrow>real\<Rightarrow>(nat\<Rightarrow>'e)\<Rightarrow>(nat\<Rightarrow>'e)"

locale native_atlas_certificates =
  fixes k :: nat and TT :: "'a\<Rightarrow>real set" and TD :: "'a\<Rightarrow>'t set"
    and tc :: "'a\<Rightarrow>'t\<Rightarrow>real"
    and VT :: "'b\<Rightarrow>'e::real_normed_vector set" and VD :: "'b\<Rightarrow>'v set"
    and vc :: "'b\<Rightarrow>'v\<Rightarrow>'e"
  assumes time_charts: "\<And>a. bij_betw (tc a) (TD a) (TT a)"
    and value_charts: "\<And>b. bij_betw (vc b) (VD b) (VT b)"
begin

definition VDomain where "VDomain b c = actual_overlap_image (VD b) (VD c) (vc b)"
definition TDomain where "TDomain a d = actual_overlap_image (TD a) (TD d) (tc a)"
definition VSpace where "VSpace a b c = TT a\<times>jet_domain k (VDomain b c)"
definition TSpace where "TSpace a d b = TDomain a d\<times>jet_domain k (VT b)"

definition value_bound :: "('a,'b,'e) atlas_certificate \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "value_bound r a b c \<longleftrightarrow>
    value_change_valid k (TT a) (VDomain b c) (VDomain c b)
      (vforward r a b c) (vbackward r a b c) (vlift r a b c) (vinverse r a b c) \<and>
    (\<forall>x\<in>VDomain b c. vforward r a b c x=actual_chart_change (VD b) (VD c) (vc b) (vc c) x) \<and>
    (\<forall>x\<in>VDomain c b. vbackward r a b c x=actual_chart_change (VD c) (VD b) (vc c) (vc b) x)"

definition time_bound :: "('a,'b,'e) atlas_certificate \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool" where
  "time_bound r a d b \<longleftrightarrow>
    bound_time_change k (VT b) (TD a) (TD d) (tc a) (tc d)
      (tforward r a d b) (tbackward r a d b) (tlift r a d b) (tinverse r a d b)"

definition regular :: "('a,'b,'e) atlas_certificate \<Rightarrow> bool" where
  "regular r \<longleftrightarrow> (\<forall>a b c. value_bound r a b c) \<and> (\<forall>a d b. time_bound r a d b)"
definition Diff1 where "Diff1 \<longleftrightarrow> (\<exists>r. regular r)"
definition ValueCov where
  "ValueCov r Rel \<longleftrightarrow> (\<forall>a b c. \<forall>p\<in>VSpace a b c.
    p\<in>Rel a b \<longleftrightarrow> value_jet_map (vlift r a b c) p\<in>Rel a c)"
definition Diff4 where "Diff4 Rel \<longleftrightarrow> (\<exists>r. regular r \<and> ValueCov r Rel)"

definition value_ambient :: "'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> (real\<times>(nat\<Rightarrow>'e)) \<Rightarrow> (real\<times>(nat\<Rightarrow>'e))" where "value_ambient a b c p=p"
definition time_ambient :: "'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> (real\<times>(nat\<Rightarrow>'e)) \<Rightarrow> (real\<times>(nat\<Rightarrow>'e))" where "time_ambient a d b p=p"

lemma diff1_has_actual_changes:
  "Diff1 \<Longrightarrow> \<forall>a b c. \<exists>r. value_bound r a b c"
  by (auto simp: Diff1_def regular_def)

lemma regular_value_domains_open:
  "regular r \<Longrightarrow> open (VDomain b c) \<and> open (VDomain c b)"
  by (auto simp: regular_def value_bound_def value_change_valid_def)

lemma regular_time_domains_open:
  "regular r \<Longrightarrow> open (TDomain a d) \<and> open (TDomain d a)"
  by (auto simp: regular_def time_bound_def bound_time_change_def time_change_valid_def TDomain_def)

lemma value_ambient_preserves_coordinates:
  "fst (value_ambient a b c p)=fst p \<and> snd (value_ambient a b c p)=snd p"
  by (simp add: value_ambient_def)

lemma time_ambient_preserves_coordinates:
  "fst (time_ambient a d b p)=fst p \<and> snd (time_ambient a d b p)=snd p"
  by (simp add: time_ambient_def)

lemma regular_value_maps_unique:
  assumes r: "regular r" and q: "regular q"
  shows "\<forall>p\<in>VSpace a b c. value_jet_map (vlift r a b c) p=value_jet_map (vlift q a b c) p"
proof -
  have rv: "value_change_valid k (TT a) (VDomain b c) (VDomain c b)
    (vforward r a b c) (vbackward r a b c) (vlift r a b c) (vinverse r a b c)"
    using r unfolding regular_def value_bound_def by blast
  have qv: "value_change_valid k (TT a) (VDomain b c) (VDomain c b)
    (vforward q a b c) (vbackward q a b c) (vlift q a b c) (vinverse q a b c)"
    using q unfolding regular_def value_bound_def by blast
  have eq: "\<forall>x\<in>VDomain b c. vforward r a b c x=vforward q a b c x"
    using r q unfolding regular_def value_bound_def by auto
  show ?thesis unfolding VSpace_def by (rule value_map_same_on_chart[OF rv qv eq])
qed

lemma value_cov_independent_of_certificate:
  assumes r: "regular r" and q: "regular q"
  shows "ValueCov r Rel \<longleftrightarrow> ValueCov q Rel"
proof -
  have maps: "value_jet_map (vlift r a b c) p=value_jet_map (vlift q a b c) p"
    if p: "p\<in>VSpace a b c" for a b c p
    using regular_value_maps_unique[OF r q, of a b c] p by blast
  show ?thesis
    unfolding ValueCov_def
    by (intro iffI allI ballI; metis maps)
qed

lemma diff4_requires_diff1: "Diff4 Rel \<Longrightarrow> Diff1"
  by (auto simp: Diff4_def Diff1_def)

lemma diff4_restricts:
  assumes r: "regular r"
  shows "Diff4 Rel \<longleftrightarrow> ValueCov r Rel"
proof
  assume "Diff4 Rel"
  then obtain q where q: "regular q" "ValueCov q Rel" unfolding Diff4_def by blast
  show "ValueCov r Rel" using value_cov_independent_of_certificate[OF q(1) r] q(2) by blast
next
  assume "ValueCov r Rel"
  with r show "Diff4 Rel" unfolding Diff4_def by blast
qed

lemma diff4_false_outside: "\<not>Diff1 \<Longrightarrow> \<not>Diff4 Rel"
  using diff4_requires_diff1 by blast

lemma restriction_image_from_bijection:
  assumes bij: "bij_betw (value_jet_map (vlift r a b c)) (VSpace a b c) (VSpace a c b)"
    and cov: "ValueCov r Rel"
  shows "value_jet_map (vlift r a b c) ` (Rel a b\<inter>VSpace a b c)=Rel a c\<inter>VSpace a c b"
proof -
  have maps: "value_jet_map (vlift r a b c) p\<in>VSpace a c b" if "p\<in>VSpace a b c" for p
    using bij that by (auto simp: bij_betw_def)
  have restricted: "\<forall>p\<in>VSpace a b c. p\<in>Rel a b\<inter>VSpace a b c \<longleftrightarrow>
    value_jet_map (vlift r a b c) p\<in>Rel a c\<inter>VSpace a c b"
    using cov maps by (auto simp: ValueCov_def)
  have onto: "value_jet_map (vlift r a b c) ` VSpace a b c=VSpace a c b"
    using bij by (simp add: bij_betw_def)
  show ?thesis by (rule Value_Jet_Lift_Algebra.relation_image[OF onto _ _ restricted]) auto
qed
end

locale finite_native_atlas_certificates = native_atlas_certificates k TT TD tc VT VD vc
  for k :: nat and TT :: "'a\<Rightarrow>real set" and TD :: "'a\<Rightarrow>'t set"
    and tc :: "'a\<Rightarrow>'t\<Rightarrow>real"
    and VT :: "'b\<Rightarrow>'e::euclidean_space set" and VD :: "'b\<Rightarrow>'v set"
    and vc :: "'b\<Rightarrow>'v\<Rightarrow>'e"
begin
lemma finite_value_relation_restriction_image:
  assumes r: "regular r" and cov: "ValueCov r Rel"
  shows "value_jet_map (vlift r a b c) ` (Rel a b\<inter>VSpace a b c)=Rel a c\<inter>VSpace a c b"
proof -
  have valid: "value_change_valid k (TT a) (VDomain b c) (VDomain c b)
    (vforward r a b c) (vbackward r a b c) (vlift r a b c) (vinverse r a b c)"
    using r unfolding regular_def value_bound_def by blast
  have bij: "bij_betw (value_jet_map (vlift r a b c)) (VSpace a b c) (VSpace a c b)"
    unfolding VSpace_def by (rule finite_value_map_bijective[OF valid])
  show ?thesis by (rule restriction_image_from_bijection[OF bij cov])
qed
end

locale trivial_native_atlas_certificates = native_atlas_certificates k TT TD tc VT VD vc
  for k :: nat and TT :: "'a\<Rightarrow>real set" and TD :: "'a\<Rightarrow>'t set"
    and tc :: "'a\<Rightarrow>'t\<Rightarrow>real"
    and VT :: "'b\<Rightarrow>'e::real_normed_vector set" and VD :: "'b\<Rightarrow>'v set"
    and vc :: "'b\<Rightarrow>'v\<Rightarrow>'e" +
  assumes zero_space: "\<forall>x::'e. x=0"
begin
lemma trivial_value_relation_restriction_image:
  assumes r: "regular r" and cov: "ValueCov r Rel"
  shows "value_jet_map (vlift r a b c) ` (Rel a b\<inter>VSpace a b c)=Rel a c\<inter>VSpace a c b"
proof -
  have valid: "value_change_valid k (TT a) (VDomain b c) (VDomain c b)
    (vforward r a b c) (vbackward r a b c) (vlift r a b c) (vinverse r a b c)"
    using r unfolding regular_def value_bound_def by blast
  have trivial: "(\<forall>x::'e. x=0) \<or> (\<forall>x::'e. x=0)" using zero_space by blast
  have bij: "bij_betw (value_jet_map (vlift r a b c)) (VSpace a b c) (VSpace a c b)"
    unfolding VSpace_def by (rule trivial_value_map_bijective[OF trivial valid])
  show ?thesis by (rule restriction_image_from_bijection[OF bij cov])
qed
end

lemmas value_relation_restriction_image =
  finite_native_atlas_certificates.finite_value_relation_restriction_image
  trivial_native_atlas_certificates.trivial_value_relation_restriction_image

ML \<open>
val roots = @{thms native_atlas_certificates.diff1_has_actual_changes
  native_atlas_certificates.regular_value_domains_open native_atlas_certificates.regular_time_domains_open
  native_atlas_certificates.value_ambient_preserves_coordinates native_atlas_certificates.time_ambient_preserves_coordinates
  native_atlas_certificates.regular_value_maps_unique native_atlas_certificates.value_cov_independent_of_certificate
  native_atlas_certificates.diff4_requires_diff1 native_atlas_certificates.diff4_restricts
  native_atlas_certificates.diff4_false_outside value_relation_restriction_image};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
