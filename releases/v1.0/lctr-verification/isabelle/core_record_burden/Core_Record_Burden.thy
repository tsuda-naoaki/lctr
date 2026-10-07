theory Core_Record_Burden
  imports Main
begin

datatype record_tag = View | Configuration | Invasiveness | CountStep | Stability
  | CellWidth | Discernibility | Communication | Coupling
datatype config_index = Bulk | Follow
datatype target_index = First | Second
datatype audit_status = Pass | Fail | Blocked | Unformed | Indeterminate

definition bulk_tags where
  "bulk_tags = {View, Configuration, Invasiveness, CountStep, Stability, CellWidth, Discernibility}"
definition following_tags where
  "following_tags = bulk_tags \<union> {Communication, Coupling}"
fun allowed where
  "allowed Bulk = bulk_tags"
| "allowed Follow = following_tags"

lemma tag_domains: "bulk_tags \<subseteq> following_tags"
  unfolding following_tags_def by auto
lemma bulk_omits_communication: "Communication \<notin> bulk_tags"
  unfolding bulk_tags_def by simp
lemma following_includes_communication: "Communication \<in> following_tags"
  unfolding following_tags_def by simp

locale record_burden =
  fixes verified :: "config_index \<Rightarrow> target_index \<Rightarrow> 'e set"
    and refs :: "'e \<Rightarrow> 'r set"
    and target :: "'e \<Rightarrow> 't"
    and tag :: "config_index \<Rightarrow> 'r \<Rightarrow> record_tag"
    and measure :: "config_index \<Rightarrow> target_index \<Rightarrow> 'r \<Rightarrow> 'v"
    and value_type :: "config_index \<Rightarrow> target_index \<Rightarrow> record_tag \<Rightarrow> 'v set"
    and states :: "config_index \<Rightarrow> target_index \<Rightarrow> 't \<Rightarrow> audit_status"
    and edge :: "('t \<times> 't) set"
    and structural :: "'t \<Rightarrow> 's"
  assumes typed: "\<And>a k e r. e \<in> verified a k \<Longrightarrow> r \<in> refs e \<Longrightarrow>
    measure a k r \<in> value_type a k (tag a r)"
begin

definition has_ref where
  "has_ref a e \<longleftrightarrow> (\<exists>r\<in>refs e. tag a r \<in> allowed a)"
definition fail_tokens where
  "fail_tokens a k = target ` {e \<in> verified a k. states a k (target e) = Fail}"
definition tokens where
  "tokens a = target ` {e. \<exists>k. e \<in> verified a k \<and> has_ref a e \<and> states a k (target e) = Fail}"
definition burden where
  "burden F = structural ` {t. \<exists>r\<in>F. (r,t) \<in> edge\<^sup>*}"
definition record_burden where
  "record_burden a = burden (tokens a)"

lemma token_witness:
  "t \<in> tokens a \<longleftrightarrow> (\<exists>k e. e \<in> verified a k \<and>
    (\<exists>r\<in>refs e. tag a r \<in> allowed a) \<and> states a k (target e) = Fail \<and> target e = t)"
  unfolding tokens_def has_ref_def by auto

lemma witness_measurement_typed:
  assumes "e \<in> verified a k" "has_ref a e"
  shows "\<exists>r\<in>refs e. tag a r \<in> allowed a \<and> measure a k r \<in> value_type a k (tag a r)"
  using assms typed unfolding has_ref_def by blast

lemma token_target_locality:
  "tokens a \<subseteq> (\<Union>k. fail_tokens a k)"
  unfolding tokens_def fail_tokens_def by auto

lemma burden_equal_iff_delta_empty:
  "record_burden Bulk = record_burden Follow \<longleftrightarrow>
    (record_burden Bulk - record_burden Follow) \<union>
    (record_burden Follow - record_burden Bulk) = {}"
  by auto

lemma singleton_burden_included:
  assumes "t \<in> tokens a"
  shows "burden {t} \<subseteq> record_burden a"
  using assms unfolding burden_def record_burden_def by auto

lemma one_sided_separation:
  assumes "t \<in> tokens a" "\<not> burden {t} \<subseteq> record_burden b"
  shows "record_burden a - record_burden b \<noteq> {}"
  using singleton_burden_included[OF assms(1)] assms(2) by blast

lemma two_sided_incomparability:
  assumes "\<exists>t\<in>tokens Bulk. \<not> burden {t} \<subseteq> record_burden Follow"
    "\<exists>t\<in>tokens Follow. \<not> burden {t} \<subseteq> record_burden Bulk"
  shows "\<not> record_burden Bulk \<subseteq> record_burden Follow \<and>
    \<not> record_burden Follow \<subseteq> record_burden Bulk"
  using assms singleton_burden_included by blast

lemma no_failed_evidence_no_tokens:
  assumes "\<And>k e. e \<in> verified a k \<Longrightarrow> states a k (target e) \<noteq> Fail"
  shows "tokens a = {}"
  using assms unfolding tokens_def by auto

lemma no_failed_evidence_no_burden:
  assumes "\<And>k e. e \<in> verified a k \<Longrightarrow> states a k (target e) \<noteq> Fail"
  shows "record_burden a = {}"
  unfolding record_burden_def
  using no_failed_evidence_no_tokens[OF assms] unfolding burden_def by simp

lemma tag_difference_alone_not_burden_difference:
  assumes "\<And>a k e. e \<in> verified a k \<Longrightarrow> states a k (target e) \<noteq> Fail"
  shows "record_burden Bulk = record_burden Follow"
  using no_failed_evidence_no_burden[OF assms] by simp

end

ML \<open>
val roots = @{thms tag_domains bulk_omits_communication following_includes_communication record_burden.token_witness record_burden.witness_measurement_typed record_burden.token_target_locality record_burden.burden_equal_iff_delta_empty record_burden.singleton_burden_included record_burden.one_sided_separation record_burden.two_sided_incomparability record_burden.no_failed_evidence_no_tokens record_burden.no_failed_evidence_no_burden record_burden.tag_difference_alone_not_burden_difference};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
