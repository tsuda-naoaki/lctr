theory Core_Trajectory_Descent_Alignment
  imports LCTR_Core_Trajectory_Descent.Core_Trajectory_Descent
begin

lemmas generated_equivalence_least = Core_Trajectory_Descent.least_equiv_minimal
lemmas image_membership_iff = trajectory_descent.exact_membership

context trajectory_descent
begin
lemma descent_iff_exact_membership:
  "desc \<longleftrightarrow> (\<forall>c\<in>C. \<forall>b\<in>B.
    ((EC``{c},EB``{b})\<in>image_rel EC EB S) = ((c,b)\<in>S))"
  using exact_membership exact_membership_implies_desc by blast
end

lemma generated_closure_descent:
  assumes cc: "(c,c')\<in>least_equiv C (generator_c C D B R Bind)"
    and bb: "(b,b')\<in>least_equiv B (generator_b C D B R Bind)"
  shows
    "((least_equiv C (generator_c C D B R Bind)``{c},
        least_equiv B (generator_b C D B R Bind)``{b})\<in>
       image_rel (least_equiv C (generator_c C D B R Bind))
         (least_equiv B (generator_b C D B R Bind)) (source_rel C D B R)) =
     ((least_equiv C (generator_c C D B R Bind)``{c'},
        least_equiv B (generator_b C D B R Bind)``{b'})\<in>
       image_rel (least_equiv C (generator_c C D B R Bind))
         (least_equiv B (generator_b C D B R Bind)) (source_rel C D B R))"
proof -
  interpret N: trajectory_descent C B "source_rel C D B R"
    "least_equiv C (generator_c C D B R Bind)"
    "least_equiv B (generator_b C D B R Bind)"
    by (rule native_trajectory_interface)
  show ?thesis by (rule N.image_descent[OF cc bb])
qed

lemma domain_is_source_image:
  "(\<exists>s. (t,s)\<in>image_rel EC EB S) \<longleftrightarrow>
    (\<exists>c b. (c,b)\<in>S \<and> EC``{c}=t)"
  unfolding image_rel_def by auto

lemma native_graph_trajectory:
  fixes S :: "('a\<times>'b) set"
  assumes single: "\<And>t s s'. (t,s)\<in>S \<Longrightarrow> (t,s')\<in>S \<Longrightarrow> s=s'"
  shows "\<exists>trajectory.
    (\<forall>t\<in>Domain S. \<forall>s. ((t,s)\<in>S) = (s=trajectory t)) \<and>
    (\<forall>other. (\<forall>t\<in>Domain S. \<forall>s. ((t,s)\<in>S) = (s=other t))
      \<longrightarrow> (\<forall>t\<in>Domain S. other t=trajectory t))"
proof (intro exI[where x="graph_map S"] conjI)
  show "\<forall>t\<in>Domain S. \<forall>s. ((t,s)\<in>S) = (s=graph_map S t)"
  proof (intro ballI allI iffI)
    fix t s
    assume t: "t\<in>Domain S" and ts: "(t,s)\<in>S"
    show "s=graph_map S t" by (rule single[OF ts graph_map_member[OF t]])
  next
    fix t s
    assume t: "t\<in>Domain S" and s: "s=graph_map S t"
    show "(t,s)\<in>S" using graph_map_member[OF t] s by simp
  qed
  show "\<forall>other. (\<forall>t\<in>Domain S. \<forall>s. ((t,s)\<in>S) = (s=other t))
      \<longrightarrow> (\<forall>t\<in>Domain S. other t=graph_map S t)"
  proof (intro allI impI)
    fix other
    assume h: "\<forall>t\<in>Domain S. \<forall>s. ((t,s)\<in>S) = (s=other t)"
    have mem: "\<And>t. t\<in>Domain S \<Longrightarrow> (t,other t)\<in>S" using h by blast
    show "\<forall>t\<in>Domain S. other t=graph_map S t"
      by (intro ballI, rule single[OF mem graph_map_member])
  qed
qed

lemma empty_relation_domain: "\<not>(\<exists>s. (t,s)\<in>image_rel EC EB {})"
  unfolding image_rel_def by simp
lemmas missing_descent_control = Core_Trajectory_Descent.missing_descent_control

ML \<open>
val roots = @{thms generated_equivalence_least image_membership_iff
  trajectory_descent.descent_iff_exact_membership generated_closure_descent domain_is_source_image
  native_graph_trajectory empty_relation_domain missing_descent_control};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
