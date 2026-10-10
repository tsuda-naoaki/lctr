theory Native_Atlas_Carriers
  imports "LCTR_Native_Atlas_Certificates.Native_Atlas_Certificates"
begin

context native_atlas_certificates
begin
lemma value_overlap_in_ambient: "VDomain b c \<subseteq> VT b"
  using value_charts[of b] by (auto simp: VDomain_def actual_overlap_image_def bij_betw_def)

lemma time_overlap_in_ambient: "TDomain a d \<subseteq> TT a"
  using time_charts[of a] by (auto simp: TDomain_def actual_overlap_image_def bij_betw_def)

lemma value_ambient_typed:
  "p\<in>VSpace a b c \<Longrightarrow> value_ambient a b c p\<in>TT a\<times>jet_domain k (VT b)"
  using value_overlap_in_ambient[of b c]
  by (auto simp: VSpace_def value_ambient_def jet_domain_def)

lemma time_ambient_typed:
  "p\<in>TSpace a d b \<Longrightarrow> time_ambient a d b p\<in>TT a\<times>jet_domain k (VT b)"
  using time_overlap_in_ambient[of a d]
  by (auto simp: TSpace_def time_ambient_def)

lemma regular_value_map_typed:
  assumes r: "regular r" and p: "p\<in>VSpace a b c"
  shows "value_jet_map (vlift r a b c) p\<in>VSpace a c b"
proof -
  have valid: "value_change_valid k (TT a) (VDomain b c) (VDomain c b)
    (vforward r a b c) (vbackward r a b c) (vlift r a b c) (vinverse r a b c)"
    using r unfolding regular_def value_bound_def by blast
  obtain t v where pair: "p=(t,v)" and t: "t\<in>TT a" and v: "v\<in>jet_domain k (VDomain b c)"
    using p by (auto simp: VSpace_def)
  have act: "value_acts k t (VDomain b c) (VDomain c b) (vforward r a b c) (vlift r a b c t)"
    using valid t unfolding value_change_valid_def by blast
  have mapped: "vlift r a b c t v\<in>jet_domain k (VDomain c b)"
    using act v unfolding value_acts_def by blast
  show ?thesis using t mapped by (simp add: pair VSpace_def value_jet_map_def)
qed

lemma regular_time_map_typed:
  assumes r: "regular r" and p: "p\<in>TSpace a d b"
  shows "time_jet_map (tforward r a d b) (tlift r a d b) p\<in>TSpace d a b"
proof -
  have valid: "time_change_valid k (VT b) (TDomain a d) (TDomain d a)
    (tforward r a d b) (tbackward r a d b) (tlift r a d b) (tinverse r a d b)"
    using r unfolding regular_def time_bound_def bound_time_change_def TDomain_def by blast
  have bij: "bij_betw (time_jet_map (tforward r a d b) (tlift r a d b)) (TSpace a d b) (TSpace d a b)"
    unfolding TSpace_def by (rule time_change_map_bijective[OF valid])
  show ?thesis using bij p by (auto simp: bij_betw_def)
qed

lemma value_cov_ambient_exact:
  "ValueCov r Rel \<longleftrightarrow> (\<forall>a b c. \<forall>p\<in>VSpace a b c.
    value_ambient a b c p\<in>Rel a b \<longleftrightarrow>
    value_ambient a c b (value_jet_map (vlift r a b c) p)\<in>Rel a c)"
  by (simp add: ValueCov_def value_ambient_def)
end

locale native_product_atlas =
  fixes k :: nat and TT :: "'a\<Rightarrow>real set" and TD :: "'a\<Rightarrow>'t set"
    and tc :: "'a\<Rightarrow>'t\<Rightarrow>real"
    and IT :: "'i\<Rightarrow>'e::real_normed_vector set" and IC :: "'i\<Rightarrow>'x set"
    and ic :: "'i\<Rightarrow>'x\<Rightarrow>'e"
    and OT :: "'j\<Rightarrow>'f::real_normed_vector set" and OC :: "'j\<Rightarrow>'y set"
    and oc :: "'j\<Rightarrow>'y\<Rightarrow>'f"
  assumes tbij: "\<And>a. bij_betw (tc a) (TD a) (TT a)"
    and ibij: "\<And>b. bij_betw (ic b) (IC b) (IT b)"
    and obij: "\<And>c. bij_betw (oc c) (OC c) (OT c)"
begin

sublocale product: native_atlas_certificates k TT TD tc
  "\<lambda>b. IT (fst b)\<times>OT (snd b)"
  "\<lambda>b. IC (fst b)\<times>OC (snd b)"
  "\<lambda>b. map_prod (ic (fst b)) (oc (snd b))"
proof
  show "bij_betw (tc a) (TD a) (TT a)" for a by (rule tbij)
  show "bij_betw (map_prod (ic (fst b)) (oc (snd b)))
    (IC (fst b)\<times>OC (snd b)) (IT (fst b)\<times>OT (snd b))" for b
    by (rule bij_betw_map_prod[OF ibij obij])
qed

lemma product_ambient_value_typed:
  "p\<in>product.VSpace a b c \<Longrightarrow>
    product.value_ambient a b c p\<in>TT a\<times>jet_domain k (IT (fst b)\<times>OT (snd b))"
  by (rule product.value_ambient_typed)
end

ML \<open>
val roots = @{thms native_atlas_certificates.value_overlap_in_ambient
  native_atlas_certificates.time_overlap_in_ambient
  native_atlas_certificates.value_ambient_typed native_atlas_certificates.time_ambient_typed
  native_atlas_certificates.regular_value_map_typed native_atlas_certificates.regular_time_map_typed
  native_atlas_certificates.value_cov_ambient_exact native_product_atlas.product_ambient_value_typed};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
