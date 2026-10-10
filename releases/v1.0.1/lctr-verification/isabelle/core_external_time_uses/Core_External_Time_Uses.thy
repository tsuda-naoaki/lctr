theory Core_External_Time_Uses
  imports "LCTR_Core_Finite_Audit.Core_Finite_Audit"
begin

datatype external_use = LogIndex | Calibration | Provenance | GeneratedPremise
datatype input_part = Formation | Evaluation | Condition
type_synonym site = "input_part \<times> token"

locale external_time_audit =
  fixes external :: "'r set"
    and usage :: "'r \<Rightarrow> external_use"
    and sites :: "'r \<Rightarrow> site set"
  assumes typed_sites: "\<And>r p t. r\<in>external \<Longrightarrow> (p,t)\<in>sites r \<Longrightarrow> t\<in>tokens"
    and faithful: "\<And>r. r\<in>external \<Longrightarrow> (sites r\<noteq>{} \<longleftrightarrow> usage r=GeneratedPremise)"
begin

definition violations where "violations = {r\<in>external. usage r=GeneratedPremise}"

lemma violation_iff_actual_site:
  "r\<in>external \<Longrightarrow> (r\<in>violations \<longleftrightarrow> sites r\<noteq>{})"
  using faithful unfolding violations_def by auto

lemma empty_iff_no_actual_sites:
  "violations={} \<longleftrightarrow> (\<forall>r\<in>external. sites r={})"
  using violation_iff_actual_site unfolding violations_def by blast

lemma empty_allows_only_metadata_uses:
  "violations={} \<Longrightarrow> r\<in>external \<Longrightarrow>
    usage r=LogIndex \<or> usage r=Calibration \<or> usage r=Provenance"
  unfolding violations_def by (cases "usage r") auto

lemma actual_site_identifies_target:
  assumes h: "r\<in>violations"
  shows "\<exists>p t. t\<in>tokens \<and> (p,t)\<in>sites r"
proof -
  have ext: "r\<in>external" using h unfolding violations_def by simp
  have nonempty: "sites r\<noteq>{}" using violation_iff_actual_site[OF ext] h by simp
  obtain p t where mem: "(p,t)\<in>sites r" using nonempty by auto
  have "t\<in>tokens" by (rule typed_sites[OF ext mem])
  then show ?thesis using mem by blast
qed

lemma every_actual_site_is_flagged:
  "r\<in>external \<Longrightarrow> s\<in>sites r \<Longrightarrow> r\<in>violations"
  using violation_iff_actual_site by blast

lemma metadata_use_has_no_premise_site:
  "r\<in>external \<Longrightarrow>
    usage r=LogIndex \<or> usage r=Calibration \<or> usage r=Provenance \<Longrightarrow>
    sites r={}"
  using faithful[of r] by auto

end

lemma native_states_depend_on_typed_inputs:
  "f=g \<Longrightarrow> e=h \<Longrightarrow> c=k \<Longrightarrow> run f e c 40=run g h k 40"
  by simp

lemma metadata_tag_alone_does_not_certify:
  defines "misleading_usage \<equiv> (\<lambda>_::unit. LogIndex)"
    and "actual_sites \<equiv> (\<lambda>_::unit. {(Formation,(0,1)::token)})"
  shows "{r. misleading_usage r=GeneratedPremise}={} \<and>
    actual_sites ()\<noteq>{} \<and>
    (\<forall>r p t. (p,t)\<in>actual_sites r \<longrightarrow> t\<in>tokens) \<and>
    \<not>(\<forall>r. actual_sites r\<noteq>{} \<longleftrightarrow> misleading_usage r=GeneratedPremise)"
  by (simp add: misleading_usage_def actual_sites_def tokens_def count_def)

ML \<open>
val roots = @{thms external_time_audit.violation_iff_actual_site
  external_time_audit.empty_iff_no_actual_sites
  external_time_audit.empty_allows_only_metadata_uses
  external_time_audit.actual_site_identifies_target
  external_time_audit.every_actual_site_is_flagged
  external_time_audit.metadata_use_has_no_premise_site
  native_states_depend_on_typed_inputs metadata_tag_alone_does_not_certify};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
