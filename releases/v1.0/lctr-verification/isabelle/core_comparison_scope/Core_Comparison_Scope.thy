theory Core_Comparison_Scope
  imports LCTR_Core_Comparison_Failure.Core_Comparison_Failure
begin

definition condition where "condition local gluing i = (if i<8 then local i else gluing)"
definition operative where "operative local gluing = ((\<forall>i\<in>{1..7::nat}. local i) \<and> gluing)"

lemma all_conditions_iff_operative:
  "(\<forall>i\<in>cmp_indices. condition local gluing i) = operative local gluing"
  unfolding condition_def operative_def cmp_indices_def by auto

lemma failure_condition_equivalence:
  "(\<not>operative local gluing) = (\<not>((\<forall>i\<in>{1..7::nat}. local i) \<and> gluing))"
  by (simp add: operative_def)

lemma assigned_failure_equivalence:
  assumes assignment: "\<And>i. i\<in>cmp_indices \<Longrightarrow> c (cmp_token i)=condition local gluing i"
  shows "(\<not>operative local gluing) = (\<not>(\<forall>i\<in>cmp_indices. c (cmp_token i)))"
  using assignment all_conditions_iff_operative[of local gluing] by simp

lemma native_first_failure_unique:
  assumes ready: "\<And>i. i\<in>cmp_indices \<Longrightarrow> f (cmp_token i) \<and> e (cmp_token i)"
    and assignment: "\<And>i. i\<in>cmp_indices \<Longrightarrow> c (cmp_token i)=condition local gluing i"
  shows "(\<not>operative local gluing) =
    (\<exists>!i. i\<in>cmp_indices \<and> run f e c 40 (cmp_token i)=Failed)"
proof -
  interpret N: native_comparison f e c by standard (fact ready)
  show ?thesis using assigned_failure_equivalence[OF assignment] N.native_failure_partition by simp
qed

definition failed_set where "failed_set s = {t\<in>tokens. s t=Failed}"
definition native_edge where "native_edge a b = (a\<in>tokens \<and> b\<in>tokens \<and> edge a b)"
definition minimal_set where
  "minimal_set s = {t\<in>failed_set s. \<forall>u\<in>failed_set s. rtranclp native_edge u t \<longrightarrow> u=t}"

lemma native_failed_class_membership:
  assumes ready: "\<And>i. i\<in>cmp_indices \<Longrightarrow> f (cmp_token i) \<and> e (cmp_token i)"
    and ii: "i\<in>cmp_indices"
  shows "(cmp_token i\<in>failed_set (run f e c 40)) = first c i"
proof -
  interpret N: native_comparison f e c by standard (fact ready)
  show ?thesis using N.R.comparison_failed_prefix[OF ii] cmp_typed[OF ii]
    by (simp add: failed_set_def)
qed

lemma native_series_partition:
  "tokens={t\<in>tokens. fst t=0}\<union>{t\<in>tokens. fst t\<noteq>0} \<and>
    {t\<in>tokens. fst t=0}\<inter>{t\<in>tokens. fst t\<noteq>0}={}"
  by auto

lemma comparison_series_exact:
  "{t\<in>tokens. fst t=0}=image cmp_token cmp_indices"
  by (auto simp: tokens_def cmp_indices_def cmp_token_def count_def)

locale recursive_native =
  fixes f e c :: "token\<Rightarrow>bool" and s :: "token\<Rightarrow>internal_state"
  assumes rec: "recurs f e c s"
begin
lemma incoming_sat:
  assumes edge: "native_edge a b" and active: "s b=SAT \<or> s b=Failed"
  shows "s a=SAT"
proof -
  have at: "s b=state (f b) (e b) (predPass s b) (c b)"
    using rec edge by (simp add: recurs_def step_def native_edge_def)
  have pass: "predPass s b" using at active by (auto simp: state_def split: if_splits)
  show ?thesis using edge pass by (auto simp: predPass_def native_edge_def)
qed

lemma strict_ancestor_sat:
  assumes path: "tranclp native_edge a b" and active: "s b=SAT \<or> s b=Failed"
  shows "s a=SAT"
  using path active
proof (induction rule: tranclp_induct)
  case (base y)
  show ?case by (rule incoming_sat[OF base.hyps base.prems])
next
  case (step y z)
  have sy: "s y=SAT" by (rule incoming_sat[OF step.hyps(2) step.prems])
  show ?case by (rule step.IH) (simp add: sy)
qed

lemma failed_antichain:
  assumes a: "a\<in>failed_set s" and b: "b\<in>failed_set s"
  shows "\<not>tranclp native_edge a b"
proof
  assume path: "tranclp native_edge a b"
  have active: "s b=SAT \<or> s b=Failed" using b by (simp add: failed_set_def)
  have "s a=SAT" by (rule strict_ancestor_sat[OF path active])
  then show False using a by (simp add: failed_set_def)
qed

lemma minimal_positions_exact: "minimal_set s=failed_set s"
proof (rule set_eqI)
  fix t
  show "(t\<in>minimal_set s)=(t\<in>failed_set s)"
  proof
    assume "t\<in>minimal_set s"
    then show "t\<in>failed_set s" by (simp add: minimal_set_def)
  next
    assume t: "t\<in>failed_set s"
    have unique: "\<And>u. u\<in>failed_set s \<Longrightarrow> rtranclp native_edge u t \<Longrightarrow> u=t"
    proof -
      fix u
      assume u: "u\<in>failed_set s" and reach: "rtranclp native_edge u t"
      have "\<not>tranclp native_edge u t" by (rule failed_antichain[OF u t])
      then show "u=t" using reach
        by (blast elim: rtranclp.cases dest: rtranclp_into_tranclp1)
    qed
    show "t\<in>minimal_set s" using t unique unfolding minimal_set_def by blast
  qed
qed
end

lemma native_failed_antichain_and_minimal:
  "(\<forall>a\<in>failed_set (run f e c 40). \<forall>b\<in>failed_set (run f e c 40).
      \<not>tranclp native_edge a b) \<and>
    minimal_set (run f e c 40)=failed_set (run f e c 40)"
proof -
  interpret R: recursive_native f e c "run f e c 40"
    by standard (fact finite_run_solves)
  show ?thesis using R.failed_antichain R.minimal_positions_exact by blast
qed

ML \<open>
val roots = @{thms all_conditions_iff_operative failure_condition_equivalence
  assigned_failure_equivalence native_first_failure_unique native_failed_class_membership
  native_series_partition comparison_series_exact native_failed_antichain_and_minimal};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
