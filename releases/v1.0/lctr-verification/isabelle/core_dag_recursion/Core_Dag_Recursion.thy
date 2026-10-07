theory Core_Dag_Recursion
  imports Main
begin

lemma wf_unique_fixed_point:
  assumes wf: "wf E" and local: "adm_wf E F"
  shows "\<exists>!s. s = F s"
proof
  show fixed: "wfrec E F = F (wfrec E F)"
    by (rule wfrec_fixpoint[OF wf local])
  fix t assume ht: "t = F t"
  show "t = wfrec E F"
  proof (rule ext)
    fix x
    show "t x = wfrec E F x"
      using wf
    proof (induction x rule: wf_induct_rule)
      case (less x)
      have same: "F t x = F (wfrec E F) x"
        using local less.IH unfolding adm_wf_def by blast
      show ?case using fun_cong[OF ht, of x] fun_cong[OF fixed, of x] same by simp
    qed
  qed
qed

definition state_update where
  "state_update V Phi f x = (if x \<in> V then Some (Phi x f) else None)"

lemma update_local:
  fixes V :: "'v set" and E :: "('v \<times> 'v) set"
    and Phi :: "'v \<Rightarrow> ('v \<Rightarrow> 's option) \<Rightarrow> 's"
  assumes "\<And>x f g. x \<in> V \<Longrightarrow>
      (\<And>y. (y,x) \<in> E \<Longrightarrow> f y = g y) \<Longrightarrow> Phi x f = Phi x g"
  shows "adm_wf E (state_update V Phi)"
proof (unfold adm_wf_def, intro allI impI)
  fix f g :: "'v \<Rightarrow> 's option" and x :: 'v
  assume eq: "\<forall>y. (y,x) \<in> E \<longrightarrow> f y = g y"
  show "state_update V Phi f x = state_update V Phi g x"
  proof (cases "x \<in> V")
    case True
    have "Phi x f = Phi x g" by (rule assms[OF True]) (use eq in blast)
    with True show ?thesis unfolding state_update_def by simp
  next
    case False
    then show ?thesis unfolding state_update_def by simp
  qed
qed

theorem finite_dag_deterministic_state_fold:
  fixes V :: "'v set" and E :: "('v \<times> 'v) set"
    and S :: "'s set" and Phi :: "'v \<Rightarrow> ('v \<Rightarrow> 's option) \<Rightarrow> 's"
  assumes fin: "finite V" and edges: "E \<subseteq> V \<times> V" and acyc: "acyclic E"
    and local: "\<And>x f g. x \<in> V \<Longrightarrow>
      (\<And>y. (y,x) \<in> E \<Longrightarrow> f y = g y) \<Longrightarrow> Phi x f = Phi x g"
    and closed: "\<And>x f. x \<in> V \<Longrightarrow>
      (\<And>y. (y,x) \<in> E \<Longrightarrow> \<exists>s\<in>S. f y = Some s) \<Longrightarrow> Phi x f \<in> S"
  shows "\<exists>!s. s = state_update V Phi s \<and> (\<forall>x\<in>V. \<exists>a\<in>S. s x = Some a)"
proof -
  have finite_E: "finite E" using fin edges finite_subset by blast
  have wf: "wf E" by (rule finite_acyclic_wf[OF finite_E acyc])
  have adm: "adm_wf E (state_update V Phi)" by (rule update_local[OF local])
  obtain s where fixed: "s = state_update V Phi s"
    and unique: "\<And>t. t = state_update V Phi t \<Longrightarrow> t = s"
    using wf_unique_fixed_point[OF wf adm] by blast
  have inside: "\<And>x. x \<in> V \<Longrightarrow> \<exists>a\<in>S. s x = Some a"
  proof -
    fix x show "x \<in> V \<Longrightarrow> \<exists>a\<in>S. s x = Some a"
      using wf
    proof (induction x rule: wf_induct_rule)
      case (less x)
      have pred: "\<And>y. (y,x) \<in> E \<Longrightarrow> \<exists>a\<in>S. s y = Some a"
        using less.IH edges by blast
      have val_in: "Phi x s \<in> S" by (rule closed[OF less.prems pred])
      have eq: "s x = Some (Phi x s)"
        using fun_cong[OF fixed, of x] less.prems unfolding state_update_def by simp
      show ?case using val_in eq by blast
    qed
  qed
  show ?thesis using fixed unique inside by blast
qed

lemma empty_vertices_empty_states:
  "\<exists>!s :: 'v \<Rightarrow> 's option. s = state_update {} Phi s \<and>
     (\<forall>x\<in>{}. \<exists>a\<in>{}. s x = Some a)"
  unfolding state_update_def by auto

definition predecessor_family where
  "predecessor_family E x S = {f. (\<forall>y. (y,x) \<in> E \<longrightarrow> f y \<in> S) \<and>
     (\<forall>y. (y,x) \<notin> E \<longrightarrow> f y = undefined)}"

definition incoming_values where
  "incoming_values E x f y = (if (y,x) \<in> E then the (f y) else undefined)"

lemma incoming_values_local:
  assumes "\<And>y. (y,x) \<in> E \<Longrightarrow> f y = g y"
  shows "incoming_values E x f = incoming_values E x g"
  using assms unfolding incoming_values_def by (intro ext) auto

lemma incoming_values_family:
  assumes "\<And>y. (y,x) \<in> E \<Longrightarrow> \<exists>a\<in>S. f y = Some a"
  shows "incoming_values E x f \<in> predecessor_family E x S"
proof -
  have inside: "\<And>y. (y,x) \<in> E \<Longrightarrow> incoming_values E x f y \<in> S"
  proof -
    fix y assume edge: "(y,x) \<in> E"
    obtain a where a: "a \<in> S" "f y = Some a" using assms[OF edge] by blast
    show "incoming_values E x f y \<in> S" using a edge unfolding incoming_values_def by simp
  qed
  show ?thesis using inside unfolding predecessor_family_def incoming_values_def by auto
qed

theorem native_predecessor_state_fold:
  fixes V :: "'v set" and E :: "('v \<times> 'v) set" and S :: "'s set"
    and Phi :: "'v \<Rightarrow> ('v \<Rightarrow> 's) \<Rightarrow> 's"
  assumes fin: "finite V" and edges: "E \<subseteq> V \<times> V" and acyc: "acyclic E"
    and typed: "\<And>x f. x \<in> V \<Longrightarrow> f \<in> predecessor_family E x S \<Longrightarrow> Phi x f \<in> S"
  shows "\<exists>!s. s = state_update V (\<lambda>x f. Phi x (incoming_values E x f)) s \<and>
    (\<forall>x\<in>V. \<exists>a\<in>S. s x = Some a)"
proof (rule finite_dag_deterministic_state_fold[OF fin edges acyc])
  fix x and f g :: "'v \<Rightarrow> 's option"
  assume "x \<in> V" and eq: "\<And>y. (y,x) \<in> E \<Longrightarrow> f y = g y"
  have inc: "incoming_values E x f = incoming_values E x g"
    by (rule incoming_values_local) (rule eq)
  show "Phi x (incoming_values E x f) = Phi x (incoming_values E x g)"
    using inc by simp
next
  fix x and f :: "'v \<Rightarrow> 's option"
  assume xv: "x \<in> V" and pred: "\<And>y. (y,x) \<in> E \<Longrightarrow> \<exists>a\<in>S. f y = Some a"
  show "Phi x (incoming_values E x f) \<in> S"
    by (rule typed[OF xv incoming_values_family[OF pred]])
qed

lemma cycle_can_have_no_solution: "\<not> (\<exists>s :: unit \<Rightarrow> bool. \<forall>x. s x = (\<not> s x))"
  by auto

lemma cycle_can_have_multiple_solutions:
  "\<exists>f g :: unit \<Rightarrow> bool. f \<noteq> g \<and> (\<forall>x. f x = f x) \<and> (\<forall>x. g x = g x)"
proof -
  have different: "(\<lambda>_ :: unit. False) \<noteq> (\<lambda>_. True)"
    by (simp add: fun_eq_iff)
  show ?thesis by (rule exI[of _ "\<lambda>_. False"], rule exI[of _ "\<lambda>_. True"]) (simp add: different)
qed

ML \<open>
  val roots = @{thms native_predecessor_state_fold finite_dag_deterministic_state_fold
    empty_vertices_empty_states cycle_can_have_no_solution cycle_can_have_multiple_solutions};
  val _ = if null (Thm_Deps.all_oracles roots) then writeln "CORE_DAG_ORACLE_CHECK: empty"
    else error "Unexpected oracle in core DAG proof roots";
\<close>

end
