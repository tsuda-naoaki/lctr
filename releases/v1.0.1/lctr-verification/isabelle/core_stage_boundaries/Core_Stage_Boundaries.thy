theory Core_Stage_Boundaries
  imports Main
begin

datatype dynamics_index = D1 | D2 | D3 | D4 | D5 | D6 | D7 | D8
datatype internal_state = SAT | Failed | NotFormed | NotEvaluable
definition state where
  "state f e p q = (if \<not> (f \<and> p) then NotFormed else if \<not> e then NotEvaluable
    else if q then SAT else Failed)"
definition recurs where
  "recurs E f e q s = (\<forall>x. s x = state (f x) (e x) (\<forall>y. E y x \<longrightarrow> s y=SAT) (q x))"

lemma recursive_failed_condition:
  assumes rec: "recurs E f e q s" and failed: "s x=Failed"
  shows "\<not> q x"
proof -
  have at_x: "s x = state (f x) (e x) (\<forall>y. E y x \<longrightarrow> s y=SAT) (q x)"
    by (rule spec[OF rec[unfolded recurs_def]])
  show ?thesis using at_x failed by (auto simp: state_def split: if_splits)
qed

locale stage_boundaries =
  fixes exactInput :: "'e \<Rightarrow> bool"
    and K :: "'e \<Rightarrow> dynamics_index \<Rightarrow> bool"
    and lawDomain diffDomain :: "'e set"
    and lawDatum :: "'e \<Rightarrow> 'law"
    and diffDatum :: "'e \<Rightarrow> 'diff"
    and lawOK :: "'law \<Rightarrow> bool"
    and diffOK :: "'diff \<Rightarrow> bool"
  assumes subdomain: "diffDomain \<subseteq> lawDomain"
begin
definition dynOperative where "dynOperative ev \<longleftrightarrow> exactInput ev \<and> (\<forall>i. K ev i)"
definition lawOperative where "lawOperative ev \<longleftrightarrow> ev\<in>lawDomain \<and> lawOK (lawDatum ev)"
definition diffOperative where
  "diffOperative ev \<longleftrightarrow> ev\<in>diffDomain \<and> lawOK (lawDatum ev) \<and> diffOK (diffDatum ev)"
definition lawFailure where "lawFailure ev \<longleftrightarrow> ev\<in>lawDomain \<and> \<not>lawOK (lawDatum ev)"
definition diffFailure where
  "diffFailure ev \<longleftrightarrow> ev\<in>diffDomain \<and> lawOK (lawDatum ev) \<and> \<not>diffOK (diffDatum ev)"

lemma dynamics_failure_not_operative:
  assumes rec: "recurs E f e q s" and assignment: "\<And>i. q (token i) \<longleftrightarrow> K ev i"
    and failure: "\<exists>i. s (token i)=Failed"
  shows "\<not>dynOperative ev"
proof
  assume "dynOperative ev"
  then have all: "\<And>i. K ev i" by (simp add: dynOperative_def)
  from failure obtain i where "s (token i)=Failed" by blast
  have "\<not>q (token i)" by (rule recursive_failed_condition[OF rec \<open>s (token i)=Failed\<close>])
  then show False using assignment[of i] all[of i] by blast
qed

lemma law_failure_requires_dynamics:
  assumes domain: "\<And>ev. ev\<in>lawDomain \<longleftrightarrow> dynOperative ev" and failure: "lawFailure ev"
  shows "dynOperative ev" using failure domain by (auto simp: lawFailure_def)

lemma dynamics_law_failures_disjoint:
  assumes domain: "\<And>ev. ev\<in>lawDomain \<longleftrightarrow> dynOperative ev"
    and rec: "recurs E f e q s" and assignment: "\<And>i. q (token i) \<longleftrightarrow> K ev i"
  shows "\<not>((\<exists>i. s (token i)=Failed) \<and> lawFailure ev)"
proof
  assume both: "(\<exists>i. s (token i)=Failed) \<and> lawFailure ev"
  have hd: "\<not>dynOperative ev" by (rule dynamics_failure_not_operative[OF rec assignment both[THEN conjunct1]])
  have hy: "dynOperative ev" by (rule law_failure_requires_dynamics[OF domain both[THEN conjunct2]])
  show False using hd hy by blast
qed

lemma law_failure_not_operative: "lawFailure ev \<Longrightarrow> \<not>lawOperative ev"
  by (simp add: lawFailure_def lawOperative_def)

lemma differential_failure_boundary:
  "diffFailure ev \<Longrightarrow> lawOperative ev \<and> \<not>diffOperative ev"
  using subdomain by (auto simp: diffFailure_def lawOperative_def diffOperative_def)

lemma differential_requires_same_law: "diffOperative ev \<Longrightarrow> lawOperative ev"
  using subdomain by (auto simp: diffOperative_def lawOperative_def)

lemma law_differential_failures_disjoint: "\<not>(lawFailure ev \<and> diffFailure ev)"
  using law_failure_not_operative differential_failure_boundary by blast

lemma differential_failure_outside_domain: "ev\<notin>diffDomain \<Longrightarrow> \<not>diffFailure ev"
  by (simp add: diffFailure_def)
end

ML \<open>
val roots = @{thms stage_boundaries.dynamics_failure_not_operative stage_boundaries.law_failure_requires_dynamics stage_boundaries.dynamics_law_failures_disjoint stage_boundaries.law_failure_not_operative stage_boundaries.differential_failure_boundary stage_boundaries.differential_requires_same_law stage_boundaries.law_differential_failures_disjoint stage_boundaries.differential_failure_outside_domain};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
