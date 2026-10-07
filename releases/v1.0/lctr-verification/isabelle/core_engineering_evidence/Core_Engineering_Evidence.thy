theory Core_Engineering_Evidence
  imports Main
begin

typedef token = "{p :: nat \<times> nat. fst p < 6 \<and> snd p < [8,3,8,9,5,5] ! fst p}"
  by (rule exI[of _ "(0,0)"]) simp

datatype internal_state = Sat | Failed | NotFormed | NotEvaluable
datatype audit_status = Pass | Fail | Blocked | Unformed | Indeterminate

locale engineering_evidence =
  fixes refs :: "'e \<Rightarrow> 'r set"
    and target :: "'e \<Rightarrow> token"
    and tag :: "'r \<Rightarrow> 'tag"
    and measure :: "'r \<Rightarrow> 'v"
    and value_type :: "'tag \<Rightarrow> 'v set"
    and condition_evidence :: "token \<Rightarrow> 'ce"
    and necessary :: "token \<Rightarrow> 'ce \<Rightarrow> bool"
    and certificate :: "'cert"
    and corresponds :: "'r set \<Rightarrow> token \<Rightarrow> 'ce \<Rightarrow> 'cert \<Rightarrow> bool"
    and formed evaluated condition :: "token \<Rightarrow> bool"
    and edge :: "token \<Rightarrow> token \<Rightarrow> bool"
    and s :: "token \<Rightarrow> internal_state"
    and burden :: "token set \<Rightarrow> 'struct set"
  assumes recursion: "\<And>t. s t = (if \<not> formed t then NotFormed
    else if \<not> (\<forall>u. edge u t \<longrightarrow> s u = Sat) then NotFormed
    else if \<not> evaluated t then NotEvaluable else if condition t then Sat else Failed)"
begin

definition valid where
  "valid e \<longleftrightarrow> refs e \<noteq> {} \<and>
    (\<forall>r\<in>refs e. measure r \<in> value_type (tag r)) \<and>
    necessary (target e) (condition_evidence (target e)) \<and>
    corresponds (refs e) (target e) (condition_evidence (target e)) certificate"
definition audit where
  "audit t = (if \<forall>u. edge u t \<longrightarrow> s u = Sat then
    (case s t of Sat \<Rightarrow> Pass | Failed \<Rightarrow> Fail | NotFormed \<Rightarrow> Unformed
      | NotEvaluable \<Rightarrow> Indeterminate) else Blocked)"
definition state where "state e = audit (target e)"
definition failed_evidence where "failed_evidence = {e. valid e \<and> state e = Fail}"
definition fail_tokens where "fail_tokens = target ` failed_evidence"

lemma references_nonempty: "valid e \<Longrightarrow> refs e \<noteq> {}"
  unfolding valid_def by simp
lemma measurements_typed: "valid e \<Longrightarrow> r \<in> refs e \<Longrightarrow> measure r \<in> value_type (tag r)"
  unfolding valid_def by blast
lemma condition_evidence_required:
  "valid e \<Longrightarrow> necessary (target e) (condition_evidence (target e))"
  unfolding valid_def by simp
lemma certificate_correspondence:
  "valid e \<Longrightarrow> corresponds (refs e) (target e) (condition_evidence (target e)) certificate"
  unfolding valid_def by simp
lemma state_is_target_state: "state e = audit (target e)"
  unfolding state_def by simp

lemma fail_iff_native_failed: "state e = Fail \<longleftrightarrow> s (target e) = Failed"
proof -
  note eq = recursion[of "target e"]
  show ?thesis using eq unfolding state_def audit_def
    by (auto split: if_splits internal_state.splits)
qed

lemma target_image_exact:
  "t \<in> fail_tokens \<longleftrightarrow> (\<exists>e. valid e \<and> state e = Fail \<and> target e = t)"
  unfolding fail_tokens_def failed_evidence_def by auto

lemma failure_image_localized: "fail_tokens \<subseteq> {t. audit t = Fail}"
  unfolding fail_tokens_def failed_evidence_def state_def by auto

lemma six_series_locality: "fail_tokens \<subseteq> (\<Union>i<6. {t. fst (Rep_token t) = i})"
  using Rep_token by auto

lemma shared_reference_targets:
  fixes es :: "bool \<Rightarrow> 'e"
  assumes "\<And>j. valid (es j)" "\<And>j. r \<in> refs (es j) \<and> state (es j) = Fail"
  shows "range (\<lambda>j. target (es j)) \<subseteq> fail_tokens"
  using assms unfolding fail_tokens_def failed_evidence_def by auto

lemma relative_burden_unique:
  "\<exists>!p. fst p = refs e \<and> snd p = burden {target e}"
  by (rule ex1I[of _ "(refs e,burden {target e})"]) auto

lemma satisfied_target_is_not_failed:
  assumes "s (target e) = Sat"
  shows "state e = Pass \<and> e \<notin> failed_evidence"
proof -
  note eq = recursion[of "target e"]
  have hp: "state e = Pass" using eq assms unfolding state_def audit_def
    by (auto split: if_splits)
  show ?thesis using hp unfolding failed_evidence_def by simp
qed

end

ML \<open>
val roots = @{thms engineering_evidence.references_nonempty engineering_evidence.measurements_typed engineering_evidence.condition_evidence_required engineering_evidence.certificate_correspondence engineering_evidence.state_is_target_state engineering_evidence.fail_iff_native_failed engineering_evidence.target_image_exact engineering_evidence.failure_image_localized engineering_evidence.six_series_locality engineering_evidence.shared_reference_targets engineering_evidence.relative_burden_unique engineering_evidence.satisfied_target_is_not_failed};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
