theory Core_Evaluation_Alignment
  imports LCTR_Core_Evaluation.Core_Evaluation
begin

lemma carrier_recursion_extension:
  assumes edges: "E \<subseteq> A\<times>A"
    and recurs: "\<And>x. x\<in>A \<Longrightarrow> s x=eval_update E f e c s x"
  defines "s' \<equiv> \<lambda>x. if x\<in>A then s x else local_state (f x) (e x) True (c x)"
  shows "s'=eval_update E f e c s' \<and> (\<forall>x\<in>A. s' x=s x)"
proof -
  have eq: "s'=eval_update E f e c s'"
  proof (rule ext)
    fix x
    have pred: "(\<forall>y. (y,x)\<in>E \<longrightarrow> s' y=Sat) =
      (\<forall>y. (y,x)\<in>E \<longrightarrow> s y=Sat)"
      using edges unfolding s'_def by auto
    show "s' x=eval_update E f e c s' x"
    proof (cases "x\<in>A")
      case True
      then show ?thesis using recurs[OF True] pred
        unfolding s'_def eval_update_def by simp
    next
      case False
      have no_pred: "\<And>y. (y,x)\<notin>E" using edges False by auto
      show ?thesis using False no_pred unfolding s'_def eval_update_def by simp
    qed
  qed
  show ?thesis using eq unfolding s'_def by simp
qed

lemma typed_argument_unique:
  assumes fin: "finite V" and edge: "E\<subseteq>V\<times>V" and acyclic: "acyclic E"
  shows "\<exists>!s. s=native_eval_update (Sigma V Spec) (argument_edges E Spec res) f e c s"
proof -
  have fe: "finite E" using fin edge finite_subset by blast
  have wf: "wf E" by (rule finite_acyclic_wf[OF fe acyclic])
  show ?thesis by (rule native_argument_unique[OF wf])
qed

lemmas state_failed_iff = Core_Evaluation.state_failed_iff
lemmas state_sat_iff = Core_Evaluation.state_sat_iff

lemma update_failed_iff:
  "(eval_update E f e c incoming x=Failed) =
    (f x \<and> e x \<and> (\<forall>y. (y,x)\<in>E \<longrightarrow> incoming y=Sat) \<and> \<not>c x)"
  unfolding eval_update_def by (rule state_failed_iff)

lemmas path_nonsat_unformed = Core_Evaluation.path_nonsat_unformed
lemmas failed_antichain = Core_Evaluation.failed_antichain
lemmas failed_minimal = Core_Evaluation.failed_minimal
lemmas failed_set_finite = Core_Evaluation.failed_set_finite
lemmas case_exact = Core_Evaluation.case_exact
lemmas coherent_section_edge = Core_Evaluation.coherent_section_edge
lemmas coherent_section_recursion = Core_Evaluation.coherent_section_recursion
lemmas failed_requires_native_domain = Core_Evaluation.failed_requires_native_domain
lemmas fibres_cover = Core_Evaluation.fibres_cover
lemmas fibres_disjoint = Core_Evaluation.fibres_disjoint

lemma failed_partition:
  assumes cover: "strict \<union> approx=UNIV" and disj: "strict \<inter> approx={}"
  shows "{x. s x=Failed} = ({x. s x=Failed}\<inter>strict)\<union>({x. s x=Failed}\<inter>approx)
    \<and> (({x. s x=Failed}\<inter>strict)\<inter>({x. s x=Failed}\<inter>approx)={})"
  using Core_Evaluation.failed_partition[OF cover disj, where s=s] by blast

ML \<open>
val roots = @{thms typed_argument_unique state_failed_iff state_sat_iff update_failed_iff
  path_nonsat_unformed failed_antichain failed_minimal failed_set_finite case_exact
  coherent_section_edge coherent_section_recursion failed_requires_native_domain
  fibres_cover fibres_disjoint failed_partition};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = if null (Thm_Deps.all_oracles @{thms carrier_recursion_extension})
  then () else error "Unexpected carrier-extension oracle";
\<close>
end
