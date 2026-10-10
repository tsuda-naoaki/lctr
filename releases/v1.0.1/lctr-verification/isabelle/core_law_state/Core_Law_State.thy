theory Core_Law_State
  imports "LCTR_Core_Evaluation.Core_Evaluation"
    "LCTR_Core_Native_Law_Family.Core_Native_Law_Family"
begin

definition law_edges where "law_edges = {(i,j). Core_Law_Failure.edge i j}"
lemma law_edges_wf: "wf law_edges"
proof (rule wf_subset[OF wf_measure])
  show "law_edges \<subseteq> measure Core_Law_Failure.rank"
    using Core_Law_Failure.edge_rank by (auto simp: law_edges_def)
qed

locale native_law_state =
  fixes selected :: bool and datum :: "('t,'a,'x,'y) law_family"
begin
definition total_condition where "total_condition i \<longleftrightarrow> selected \<and> condition datum i"
definition ancestor_all where "ancestor_all i \<longleftrightarrow>
  (\<forall>j. Core_Law_Failure.ancestor j i \<longrightarrow> total_condition j)"
definition minimal_class where "minimal_class i \<longleftrightarrow> selected \<and> ancestor_all i \<and> \<not> total_condition i"
definition failure where "failure \<longleftrightarrow> selected \<and> \<not> (\<forall>i. total_condition i)"
definition ideal_state :: "law_node \<Rightarrow> Core_Evaluation.eval_state" where
  "ideal_state i = (if total_condition i then Core_Evaluation.Sat
    else if selected \<and> ancestor_all i then Core_Evaluation.Failed else Core_Evaluation.Unformed)"
definition law_update where
  "law_update q = Core_Evaluation.eval_update law_edges (\<lambda>_. selected) (\<lambda>_. True) total_condition q"

lemma ideal_sat_iff: "ideal_state i = Core_Evaluation.Sat \<longleftrightarrow> total_condition i"
  by (auto simp: ideal_state_def)
lemma total_ancestor_condition:
  "tranclp Core_Law_Failure.edge i j \<Longrightarrow> total_condition j \<Longrightarrow> total_condition i"
  using Core_Native_Law_Family.ancestor_conditions_hold[of i j datum]
  unfolding total_condition_def by blast
lemma direct_pass_iff_ancestors:
  "(\<forall>j. Core_Law_Failure.edge j i \<longrightarrow> ideal_state j = Core_Evaluation.Sat) \<longleftrightarrow> ancestor_all i"
  by (cases i; auto simp: ideal_sat_iff ancestor_all_def total_condition_def
    Core_Law_Failure.ancestor_def Core_Law_Failure.edge_def K3_def K5_def)
lemma ideal_recursion: "ideal_state = law_update ideal_state"
proof (rule ext)
  fix i
  have prior: "(\<forall>j. (j,i) \<in> law_edges \<longrightarrow> ideal_state j = Core_Evaluation.Sat) = ancestor_all i"
    using direct_pass_iff_ancestors[of i] by (simp add: law_edges_def)
  have good: "total_condition i \<Longrightarrow> selected \<and> ancestor_all i"
  proof
    assume h: "total_condition i"
    show selected using h by (simp add: total_condition_def)
    show "ancestor_all i"
      unfolding ancestor_all_def
      by (intro allI impI, rule total_ancestor_condition[OF _ h])
        (simp add: Core_Law_Failure.ancestors_exact)
  qed
  have rhs: "law_update ideal_state i =
    Core_Evaluation.local_state selected True (ancestor_all i) (total_condition i)"
    unfolding law_update_def Core_Evaluation.eval_update_def by (simp only: prior)
  show "ideal_state i = law_update ideal_state i"
    using good unfolding rhs ideal_state_def Core_Evaluation.local_state_def by auto
qed
lemma recursive_state_unique:
  assumes recurs: "q = law_update q"
  shows "q = ideal_state"
proof -
  have unique: "\<exists>!r. r = law_update r"
    unfolding law_update_def by (rule Core_Evaluation.unique_state_recursion[OF law_edges_wf])
  show ?thesis using unique recurs ideal_recursion by blast
qed
lemma ideal_failed_iff: "ideal_state i = Core_Evaluation.Failed \<longleftrightarrow> minimal_class i"
  by (auto simp: ideal_state_def minimal_class_def)
lemma recursive_failed_iff:
  "q = law_update q \<Longrightarrow> (q i = Core_Evaluation.Failed \<longleftrightarrow> minimal_class i)"
  using recursive_state_unique[of q] ideal_failed_iff[of i] by simp
lemma recursive_completion_iff:
  assumes recurs: "q = law_update q" and sel: selected
  shows "(\<forall>i. q i = Core_Evaluation.Sat) \<longleftrightarrow> all_conditions datum"
proof -
  have eq: "q = ideal_state" by (rule recursive_state_unique[OF recurs])
  have sat: "(\<forall>i. q i = Core_Evaluation.Sat) \<longleftrightarrow> (\<forall>i. total_condition i)"
    by (simp only: eq ideal_sat_iff)
  have all: "(\<forall>i. total_condition i) \<longleftrightarrow> all_conditions datum"
    unfolding total_condition_def by (simp add: sel all_conditions_exact)
  show ?thesis using sat all by blast
qed
lemma recursive_failure_exists_iff:
  assumes recurs: "q = law_update q"
  shows "(\<exists>i. q i = Core_Evaluation.Failed) \<longleftrightarrow> failure"
proof -
  have cover: "failure \<longleftrightarrow> (\<exists>i. minimal_class i)"
    using Core_Law_Failure.failure_cover[of selected total_condition]
    by (simp add: failure_def minimal_class_def ancestor_all_def
      Core_Law_Failure.fails_def Core_Law_Failure.minimal_def Core_Law_Failure.ancestors_hold_def)
  show ?thesis using recursive_failed_iff[OF recurs] cover by blast
qed
end

ML \<open>
val roots = @{thms native_law_state.ideal_sat_iff native_law_state.total_ancestor_condition
  native_law_state.direct_pass_iff_ancestors native_law_state.ideal_recursion
  native_law_state.recursive_state_unique native_law_state.ideal_failed_iff
  native_law_state.recursive_failed_iff native_law_state.recursive_completion_iff
  native_law_state.recursive_failure_exists_iff};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int (length roots));
\<close>
end
