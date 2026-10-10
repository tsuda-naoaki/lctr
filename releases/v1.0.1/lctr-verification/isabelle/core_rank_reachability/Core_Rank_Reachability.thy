theory Core_Rank_Reachability
 imports Main
begin

lemma path_increases:
 assumes step: "\<And>a b. (a,b)\<in>E \<Longrightarrow> (r a,r b)\<in>P"
 and tr: "trans P" and path: "(a,b)\<in>E\<^sup>+"
 shows "(r a,r b)\<in>P"
 using path
proof (induction rule: trancl_induct)
 case (base y)
 then show ?case by (rule step)
next
 case (step y z)
 then show ?case using assms(1) tr unfolding trans_def by blast
qed

lemma rank_acyclic:
 assumes step: "\<And>a b. (a,b)\<in>E \<Longrightarrow> (r a,r b)\<in>P"
 and tr: "trans P" and ir: "irrefl P"
 shows "acyclic E"
proof (unfold acyclic_def, intro allI notI)
 fix a assume p: "(a,a)\<in>E\<^sup>+"
 have "(r a,r a)\<in>P" by (rule path_increases[OF step tr p])
 then show False using ir unfolding irrefl_def by blast
qed

lemma rank_partial_order:
 assumes step: "\<And>a b. (a,b)\<in>E \<Longrightarrow> (r a,r b)\<in>P"
 and tr: "trans P" and ir: "irrefl P"
 shows "refl_on UNIV (E\<^sup>* ) \<and> trans (E\<^sup>* ) \<and> antisym (E\<^sup>* )"
proof -
 have ac: "acyclic E" by (rule rank_acyclic[OF step tr ir])
 have an: "antisym (E\<^sup>* )" by (rule acyclic_impl_antisym_rtrancl[OF ac])
 show ?thesis using an
  unfolding refl_on_def trans_def by (blast intro: rtrancl_trans)
qed

ML \<open>
val roots = @{thms path_increases rank_acyclic rank_partial_order};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
