theory Core_Native_Time_Conditions
  imports "LCTR_Core_Chart_Overlaps.Core_Chart_Overlaps"
begin

record 'v time_change_certificate =
  cert_forward :: "real\<Rightarrow>real"
  cert_backward :: "real\<Rightarrow>real"
  cert_lift :: "real\<Rightarrow>(nat\<Rightarrow>'v)\<Rightarrow>(nat\<Rightarrow>'v)"
  cert_inverse_lift :: "real\<Rightarrow>(nat\<Rightarrow>'v)\<Rightarrow>(nat\<Rightarrow>'v)"

definition valid_time_certificate where
  "valid_time_certificate k Z P Q b \<longleftrightarrow>
    open P \<and> open Q \<and> cert_forward b ` P\<subseteq>Q \<and> cert_backward b ` Q\<subseteq>P \<and>
    higher_differentiable_on P (cert_forward b) k \<and> higher_differentiable_on Q (cert_backward b) k \<and>
    (\<forall>a\<in>P. cert_backward b (cert_forward b a)=a) \<and>
    (\<forall>a\<in>Q. cert_forward b (cert_backward b a)=a) \<and>
    (\<forall>a\<in>P. time_acts k a (cert_forward b a) Z (cert_backward b) (cert_lift b a)) \<and>
    (\<forall>a\<in>P. time_acts k (cert_forward b a) a Z (cert_forward b) (cert_inverse_lift b (cert_forward b a)))"
definition certificate_map where "certificate_map b p = (cert_forward b (fst p),cert_lift b (fst p) (snd p))"
definition ambient_coordinate :: "'a\<Rightarrow>'a" where "ambient_coordinate p=p"

lemma certificate_bijection:
  assumes b: "valid_time_certificate k Z P Q b"
  shows "bij_betw (certificate_map b) (P\<times>jet_domain k Z) (Q\<times>jet_domain k Z)"
proof -
  have h: "bij_betw (\<lambda>(a,v). (cert_forward b a,cert_lift b a v)) (P\<times>jet_domain k Z) (Q\<times>jet_domain k Z)"
    by (rule time_jet_full_domain_bijective[where f="cert_forward b" and g="cert_backward b"
      and J="cert_lift b" and K="cert_inverse_lift b"])
      (use b in \<open>auto simp: valid_time_certificate_def\<close>)
  show ?thesis using h by (simp add: certificate_map_def[abs_def] split_def)
qed

context coordinate_overlaps
begin
definition bound_time_certificate where
  "bound_time_certificate k Z b \<longleftrightarrow>
    valid_time_certificate k Z source_coordinate_domain target_coordinate_domain b \<and>
    (\<forall>a\<in>source_coordinate_domain. cert_forward b a=chart_map a) \<and>
    (\<forall>a\<in>target_coordinate_domain. cert_backward b a=chart_inverse a)"
definition rep_cov where
  "rep_cov k Z b R S \<longleftrightarrow> (\<forall>p\<in>source_coordinate_domain\<times>jet_domain k Z.
    ambient_coordinate p\<in>R \<longleftrightarrow> ambient_coordinate (certificate_map b p)\<in>S)"

lemma bound_time_maps_unique:
  assumes b: "bound_time_certificate k Z b" and q: "bound_time_certificate k Z q"
  shows "\<forall>p\<in>source_coordinate_domain\<times>jet_domain k Z. certificate_map b p=certificate_map q p"
proof (intro ballI)
  fix p assume p: "p\<in>source_coordinate_domain\<times>jet_domain k Z"
  have a: "fst p\<in>source_coordinate_domain" and v: "snd p\<in>jet_domain k Z" using p by auto
  have feq: "cert_forward b (fst p)=cert_forward q (fst p)"
    using b q a by (auto simp: bound_time_certificate_def)
  have target: "cert_forward q (fst p)\<in>target_coordinate_domain" and opened: "open target_coordinate_domain"
    using q a by (auto simp: bound_time_certificate_def valid_time_certificate_def)
  obtain c where c: "curve_ck_at k (fst p) c" "c (fst p)\<in>Z" "jet k (fst p) c=snd p"
    by (rule jet_domain_realization[OF v])
  have actb: "time_acts k (fst p) (cert_forward b (fst p)) Z (cert_backward b) (cert_lift b (fst p))"
    using b a unfolding bound_time_certificate_def valid_time_certificate_def by blast
  have actq: "time_acts k (fst p) (cert_forward q (fst p)) Z (cert_backward q) (cert_lift q (fst p))"
    using q a unfolding bound_time_certificate_def valid_time_certificate_def by blast
  have ev: "eventually (\<lambda>x. x\<in>target_coordinate_domain) (nhds (cert_forward q (fst p)))"
    by (rule eventually_nhds_in_open[OF opened target])
  have eq: "eventually (\<lambda>x. (c \<circ> cert_backward b) x=(c \<circ> cert_backward q) x) (nhds (cert_forward q (fst p)))"
    using ev by eventually_elim (use b q in \<open>auto simp: bound_time_certificate_def\<close>)
  have jeq: "jet k (cert_forward q (fst p)) (c \<circ> cert_backward b)=jet k (cert_forward q (fst p)) (c \<circ> cert_backward q)"
    by (rule jet_germ[OF eq])
  show "certificate_map b p=certificate_map q p"
    using time_acts_apply[OF actb c(1,2)] time_acts_apply[OF actq c(1,2)] c(3) jeq feq
    by (simp add: certificate_map_def)
qed

lemma rep_domain_formula:
  "source_coordinate_domain = {theta. \<exists>x\<in>D. h x\<in>E \<and> c x=theta}"
  by (rule coordinate_domain_formula)

lemma rep_change_from_actual_time_map:
  assumes b: "bound_time_certificate k Z b" and x: "x\<in>source_overlap"
  shows "cert_forward b (c x)=d (h x)"
proof -
  have cx: "c x\<in>source_coordinate_domain" using x by (auto simp: source_coordinate_domain_def)
  show ?thesis using b cx chart_forward_formula[OF x] by (simp add: bound_time_certificate_def)
qed

lemma rep_ambient_coordinates:
  assumes p: "p\<in>source_coordinate_domain\<times>jet_domain k Z"
  shows "fst (ambient_coordinate p)=fst p \<and> snd (ambient_coordinate p)=snd p \<and>
    ambient_coordinate p\<in>U\<times>jet_domain k Z"
  using p cb by (auto simp: ambient_coordinate_def source_coordinate_domain_def source_overlap_def bij_betw_def)

lemma rep_cov_independent_of_certificate:
  assumes b: "bound_time_certificate k Z b" and q: "bound_time_certificate k Z q"
  shows "rep_cov k Z b R S \<longleftrightarrow> rep_cov k Z q R S"
  using bound_time_maps_unique[OF b q] unfolding rep_cov_def by simp

lemma rep_relation_restriction_image:
  assumes b: "bound_time_certificate k Z b" and cov: "rep_cov k Z b R S"
  shows "certificate_map b ` (R\<inter>(source_coordinate_domain\<times>jet_domain k Z)) =
    S\<inter>(target_coordinate_domain\<times>jet_domain k Z)"
proof -
  have bij: "bij_betw (certificate_map b) (source_coordinate_domain\<times>jet_domain k Z) (target_coordinate_domain\<times>jet_domain k Z)"
    by (rule certificate_bijection) (use b in \<open>simp add: bound_time_certificate_def\<close>)
  show ?thesis by (rule ambient_restriction_image[OF bij]) (use cov in \<open>simp add: rep_cov_def ambient_coordinate_def\<close>)
qed

lemma rep_time_change_preserves_value:
  assumes b: "bound_time_certificate k Z b" and p: "p\<in>source_coordinate_domain\<times>jet_domain k Z"
  shows "snd (ambient_coordinate (certificate_map b p)) 0=snd (ambient_coordinate p) 0"
proof -
  have a: "fst p\<in>source_coordinate_domain" and v: "snd p\<in>jet_domain k Z" using p by auto
  obtain c where c: "curve_ck_at k (fst p) c" "c (fst p)\<in>Z" "jet k (fst p) c=snd p"
    by (rule jet_domain_realization[OF v])
  have act: "time_acts k (fst p) (cert_forward b (fst p)) Z (cert_backward b) (cert_lift b (fst p))"
    using b a unfolding bound_time_certificate_def valid_time_certificate_def by blast
  have inv: "cert_backward b (cert_forward b (fst p))=fst p" using act by (simp add: time_acts_def)
  have j: "cert_lift b (fst p) (snd p)=jet k (cert_forward b (fst p)) (c \<circ> cert_backward b)"
    using time_acts_apply[OF act c(1,2)] c(3) by simp
  have z: "jet k (fst p) c 0=snd p 0" using c(3) by simp
  show ?thesis using j z inv
    by (simp add: ambient_coordinate_def certificate_map_def jet_def restrict_def)
qed
end

ML \<open>
val roots = @{thms coordinate_overlaps.bound_time_maps_unique coordinate_overlaps.rep_domain_formula
  coordinate_overlaps.rep_change_from_actual_time_map coordinate_overlaps.rep_ambient_coordinates
  coordinate_overlaps.rep_cov_independent_of_certificate coordinate_overlaps.rep_relation_restriction_image
  coordinate_overlaps.rep_time_change_preserves_value};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
