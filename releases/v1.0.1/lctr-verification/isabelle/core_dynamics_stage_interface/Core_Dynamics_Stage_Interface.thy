theory Core_Dynamics_Stage_Interface
  imports "LCTR_Core_Dynamics_Tokens.Core_Dynamics_Tokens"
begin

record conditions =
  generated_order :: bool
  trajectory_descent :: bool
  trajectory_function :: bool
  observable_descent :: bool
  change_commutation :: bool
  incomparability_transitive :: bool
  real_embedding :: bool
  trajectory_factor :: bool

definition indexed where
 "indexed p i = ([generated_order p, trajectory_descent p, trajectory_function p,
   observable_descent p, change_commutation p, incomparability_transitive p,
   real_embedding p, trajectory_factor p] ! i)"
definition canonical_bundle where
 "canonical_bundle p = (generated_order p \<and> trajectory_descent p \<and> trajectory_function p)"
definition law_bundle where
 "law_bundle p = (canonical_bundle p \<and> observable_descent p \<and> change_commutation p)"
definition all_conditions where
 "all_conditions p = (law_bundle p \<and> incomparability_transitive p \<and>
    real_embedding p \<and> trajectory_factor p)"

lemma index_assignment:
 "indexed p 0 = generated_order p \<and> indexed p 1 = trajectory_descent p \<and>
  indexed p 2 = trajectory_function p \<and> indexed p 3 = observable_descent p \<and>
  indexed p 4 = change_commutation p \<and> indexed p 5 = incomparability_transitive p \<and>
  indexed p 6 = real_embedding p \<and> indexed p 7 = trajectory_factor p"
 by (simp add: indexed_def)
lemma canonical_bundle:
 "canonical_bundle p \<longleftrightarrow> indexed p 0 \<and> indexed p 1 \<and> indexed p 2"
 by (simp add: canonical_bundle_def indexed_def)
lemma law_bundle:
 "law_bundle p \<longleftrightarrow> canonical_bundle p \<and> indexed p 3 \<and> indexed p 4"
 by (simp add: law_bundle_def indexed_def)
lemma all_conditions:
 "all_conditions p \<longleftrightarrow> (\<forall>i<8. indexed p i)"
proof -
 have split: "\<And>i::nat. i<8 \<Longrightarrow> i=0 \<or> i=1 \<or> i=2 \<or> i=3 \<or>
   i=4 \<or> i=5 \<or> i=6 \<or> i=7" by arith
 have bounds: "(0::nat)<8 \<and> (1::nat)<8 \<and> (2::nat)<8 \<and> (3::nat)<8 \<and>
   (4::nat)<8 \<and> (5::nat)<8 \<and> (6::nat)<8 \<and> (7::nat)<8" by simp
 show ?thesis
  unfolding all_conditions_def law_bundle_def canonical_bundle_def
  using index_assignment[of p] split bounds by blast
qed

lemma readiness_exact:
 assumes form: "\<And>i. i<8 \<Longrightarrow> f(dyn_token i) \<Longrightarrow> exact_input"
 and i: "i<8" and ready: "dyn_ready f e st i"
 shows "exact_input"
 using form[OF i] ready unfolding dyn_ready_def by blast
lemma failure_exact:
 assumes rec: "st=eval_update edges f e c st"
 and form: "\<And>i. i<8 \<Longrightarrow> f(dyn_token i) \<Longrightarrow> exact_input"
 and i: "i<8" and failed: "st(dyn_token i)=Failed"
 shows "exact_input"
proof -
 have ready: "dyn_ready f e st i"
  using recursive_failure[OF rec, where i=i] failed by blast
 show ?thesis by (rule readiness_exact[OF form i ready])
qed
lemma outside_exact_unformed:
 assumes rec: "st=eval_update edges f e c st"
 and form: "\<And>i. i<8 \<Longrightarrow> f(dyn_token i) \<Longrightarrow> exact_input"
 and outside: "\<not>exact_input" and i: "i<8"
 shows "st(dyn_token i)=Unformed"
proof -
 have no: "\<not>f(dyn_token i)" using form[OF i] outside by blast
 show ?thesis using fun_cong[OF rec, of "dyn_token i"]
  by (simp add: eval_update_def local_state_def no)
qed
lemma condition_failure:
 assumes rec: "st=eval_update edges f e c st" and i: "i<8"
 and assignment: "\<And>j. j<8 \<Longrightarrow> c(dyn_token j)=indexed p j"
 shows "dyn_token i\<in>failed_strict st \<longleftrightarrow> dyn_ready f e st i \<and> \<not>indexed p i"
 by (rule condition_correspondence[where K="indexed p", OF rec i assignment[OF i]])

ML \<open>
val roots = @{thms index_assignment canonical_bundle law_bundle all_conditions
 readiness_exact failure_exact outside_exact_unformed condition_failure};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
