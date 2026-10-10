theory Core_Evaluation
  imports LCTR_Core_Dag_Recursion.Core_Dag_Recursion
begin

datatype eval_state = Unformed | Unevaluable | Sat | Failed

definition local_state where
  "local_state formed evaluated prior condition =
    (if \<not> (formed \<and> prior) then Unformed
     else if \<not> evaluated then Unevaluable
     else if condition then Sat else Failed)"

definition eval_update where
  "eval_update E f e c s x = local_state (f x) (e x) (\<forall>y. (y,x)\<in>E \<longrightarrow> s y = Sat) (c x)"

lemma eval_update_local: "adm_wf E (eval_update E f e c)"
  unfolding adm_wf_def eval_update_def
  by (intro allI impI) (metis)

theorem unique_state_recursion:
  assumes "wf E"
  shows "\<exists>!s. s = eval_update E f e c s"
  by (rule wf_unique_fixed_point[OF assms eval_update_local])

definition argument_edges where
  "argument_edges E Spec res = {((y,j),(x,i)). (y,x)\<in>E \<and> i\<in>Spec x \<and> j = res x y i}"

lemma argument_edges_wf:
  assumes "wf E"
  shows "wf (argument_edges E Spec res)"
proof -
  have "wf (inv_image E fst)" by (rule wf_inv_image[OF assms])
  then show ?thesis by (rule wf_subset) (auto simp: argument_edges_def inv_image_def)
qed

theorem typed_argument_unique:
  assumes "finite V" "E \<subseteq> V \<times> V" "acyclic E"
  shows "\<exists>!s. s = eval_update (argument_edges E Spec res) f e c s"
proof -
  have "finite E" using assms(1,2) finite_subset by blast
  then have "wf E" using assms(3) by (rule finite_acyclic_wf)
  then show ?thesis by (rule unique_state_recursion[OF argument_edges_wf])
qed

definition native_eval_update where
  "native_eval_update A E f e c s x = (if x\<in>A then
    Some (local_state (f x) (e x) (\<forall>y. (y,x)\<in>E \<longrightarrow> s y = Some Sat) (c x)) else None)"

lemma native_eval_local: "adm_wf E (native_eval_update A E f e c)"
  unfolding adm_wf_def native_eval_update_def by (intro allI impI) metis

theorem native_argument_unique:
  assumes "wf E"
  shows "\<exists>!s. s = native_eval_update A (argument_edges E Spec res) f e c s"
  by (rule wf_unique_fixed_point[OF argument_edges_wf[OF assms] native_eval_local])

lemma argument_edges_typed:
  assumes edges: "E \<subseteq> V \<times> V"
    and typed: "\<And>x y i. (y,x)\<in>E \<Longrightarrow> i\<in>Spec x \<Longrightarrow> res x y i\<in>Spec y"
  shows "argument_edges E Spec res \<subseteq> (Sigma V Spec) \<times> (Sigma V Spec)"
  using edges typed unfolding argument_edges_def by auto

lemma native_state_range:
  assumes "s = native_eval_update A E f e c s"
  shows "x\<in>A \<Longrightarrow> \<exists>q. s x = Some q" and "x\<notin>A \<Longrightarrow> s x = None"
  using fun_cong[OF assms, of x] unfolding native_eval_update_def by auto

lemma native_lift_recursion:
  assumes recur: "s = eval_update E f e c s" and edges: "E \<subseteq> A \<times> A"
  shows "(\<lambda>x. if x\<in>A then Some (s x) else None) =
    native_eval_update A E f e c (\<lambda>x. if x\<in>A then Some (s x) else None)"
proof (rule ext)
  fix x
  have pred: "(\<forall>y. (y,x)\<in>E \<longrightarrow> (if y\<in>A then Some (s y) else None) = Some Sat)
      = (\<forall>y. (y,x)\<in>E \<longrightarrow> s y = Sat)"
    using edges by auto
  show "(if x\<in>A then Some (s x) else None) =
    native_eval_update A E f e c (\<lambda>x. if x\<in>A then Some (s x) else None) x"
    using fun_cong[OF recur, of x] pred unfolding native_eval_update_def eval_update_def by simp
qed

lemma state_failed_iff:
  "local_state f e p c = Failed \<longleftrightarrow> f \<and> e \<and> p \<and> \<not> c"
  unfolding local_state_def by auto

lemma state_sat_iff:
  "local_state f e p c = Sat \<longleftrightarrow> f \<and> e \<and> p \<and> c"
  unfolding local_state_def by auto

lemma direct_nonsat_unformed:
  assumes recur: "s = eval_update E f e c s" and edge: "(a,b)\<in>E" and ns: "s a \<noteq> Sat"
  shows "s b = Unformed"
proof -
  have "\<not> (\<forall>y. (y,b)\<in>E \<longrightarrow> s y = Sat)" using edge ns by blast
  then show ?thesis using fun_cong[OF recur, of b] unfolding eval_update_def local_state_def by simp
qed

theorem path_nonsat_unformed:
  assumes recur: "s = eval_update E f e c s" and path: "(a,b)\<in>E\<^sup>+" and ns: "s a \<noteq> Sat"
  shows "s b = Unformed"
  using path
proof (induction rule: trancl_induct)
  case (base y)
  show ?case by (rule direct_nonsat_unformed[OF recur base ns])
next
  case (step y z)
  have ns_y: "s y \<noteq> Sat" using step.IH by simp
  show ?case by (rule direct_nonsat_unformed[OF recur step.hyps(2) ns_y])
qed

theorem failed_antichain:
  assumes "s = eval_update E f e c s" "s a = Failed" "s b = Failed"
  shows "(a,b)\<notin>E\<^sup>+"
proof
  assume edge: "(a,b)\<in>E\<^sup>+"
  have ns: "s a \<noteq> Sat" using assms(2) by simp
  have "s b = Unformed" by (rule path_nonsat_unformed[OF assms(1) edge ns])
  then show False using assms(3) by simp
qed

lemma failed_minimal:
  assumes recur: "s = eval_update E f e c s" and ha: "s a = Failed" and hb: "s b = Failed"
    and le: "(a,b)\<in>E\<^sup>*"
  shows "a=b"
  using le failed_antichain[OF recur ha hb] by (simp add: rtrancl_eq_or_trancl)

lemma failed_set_finite:
  assumes "finite V"
  shows "finite {x\<in>V. s x = Failed}"
  using assms by simp

datatype failure_case = Absent | Unique | Parallel

definition failure_case_of where
  "failure_case_of (n::nat) = (if n=0 then Absent else if n=1 then Unique else Parallel)"

lemma case_exact:
  "(failure_case_of n = Absent \<longleftrightarrow> n=0) \<and>
   (failure_case_of n = Unique \<longleftrightarrow> n=1) \<and>
   (failure_case_of n = Parallel \<longleftrightarrow> 2\<le>n)"
  unfolding failure_case_of_def by auto

lemma coherent_section_edge:
  assumes "(a,b)\<in>E" "selected b\<in>Spec b" "res b a (selected b) = selected a"
  shows "((a,selected a),(b,selected b)) \<in> argument_edges E Spec res"
  using assms unfolding argument_edges_def by auto

lemma coherent_section_recursion:
  assumes recur: "s = eval_update (argument_edges E Spec res) f e c s"
    and selected: "\<And>x. chosen x\<in>Spec x"
    and coherent: "\<And>x y. (y,x)\<in>E \<Longrightarrow> res x y (chosen x) = chosen y"
  shows "(\<lambda>x. s (x,chosen x)) =
    eval_update E (\<lambda>x. f (x,chosen x)) (\<lambda>x. e (x,chosen x)) (\<lambda>x. c (x,chosen x)) (\<lambda>x. s (x,chosen x))"
proof (rule ext)
  fix x
  have pred: "(\<forall>a. (a,(x,chosen x))\<in>argument_edges E Spec res \<longrightarrow> s a = Sat)
      = (\<forall>y. (y,x)\<in>E \<longrightarrow> s (y,chosen y) = Sat)"
    using selected coherent unfolding argument_edges_def by auto
  show "s (x,chosen x) = eval_update E (\<lambda>x. f (x,chosen x)) (\<lambda>x. e (x,chosen x)) (\<lambda>x. c (x,chosen x)) (\<lambda>x. s (x,chosen x)) x"
    using fun_cong[OF recur, of "(x,chosen x)"] pred unfolding eval_update_def by simp
qed

lemma failed_requires_native_domain:
  assumes recur: "s = eval_update E f e c s"
    and typed: "\<And>x. f x \<Longrightarrow> e x \<Longrightarrow> (\<forall>y. (y,x)\<in>E \<longrightarrow> s y = Sat) \<Longrightarrow> D x"
    and failed: "s x = Failed"
  shows "D x"
proof -
  have ev: "local_state (f x) (e x) (\<forall>y. (y,x)\<in>E \<longrightarrow> s y = Sat) (c x) = Failed"
    using fun_cong[OF recur, of x] failed unfolding eval_update_def by simp
  have facts: "f x \<and> e x \<and> (\<forall>y. (y,x)\<in>E \<longrightarrow> s y = Sat) \<and> \<not> c x"
    by (rule state_failed_iff[THEN iffD1, OF ev])
  show ?thesis using typed[of x] facts by blast
qed

lemma fibres_cover: "(\<Union>q::eval_state. {x\<in>R. s x = q}) = R" by auto

lemma fibres_disjoint:
  assumes "q \<noteq> r"
  shows "{x\<in>R. s x = q} \<inter> {x\<in>R. s x = r} = {}"
  using assms by auto

lemma failed_partition:
  assumes "strict \<union> approx = UNIV" "strict \<inter> approx = {}"
  shows "{x. s x = Failed} = ({x. s x = Failed} \<inter> strict) \<union> ({x. s x = Failed} \<inter> approx)"
    and "({x. s x = Failed} \<inter> strict) \<inter> ({x. s x = Failed} \<inter> approx) = {}"
  using assms by auto

ML \<open>
  val roots = @{thms typed_argument_unique native_argument_unique argument_edges_typed state_failed_iff state_sat_iff
    path_nonsat_unformed failed_antichain failed_minimal failed_set_finite case_exact
    coherent_section_edge coherent_section_recursion failed_requires_native_domain
    native_state_range native_lift_recursion fibres_cover fibres_disjoint failed_partition};
  val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected core evaluation oracle";
\<close>
end
