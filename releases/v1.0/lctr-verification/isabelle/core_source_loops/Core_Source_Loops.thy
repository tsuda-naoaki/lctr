theory Core_Source_Loops
  imports "LCTR_Core_Comparison_Integration.Core_Comparison_Integration"
begin

fun source_atom where
  "source_atom (Source u v) = True" |
  "source_atom (Forward u v) = False" |
  "source_atom (Backward u v) = False"
definition source_only where "source_only es = (\<forall>e\<in>set es. source_atom e)"
definition transport_only where "transport_only es = (\<forall>e\<in>set es. \<not>source_atom e)"

context native_comparison
begin

interpretation W: typed_actions "regions D f" "{e. admitted adm e}" initial terminal inverted "cmp_act D f tr"
proof
  fix e assume "e\<in>{e. admitted adm e}"
  then show "inverted e\<in>{e. admitted adm e}" by (cases e) auto
next
  fix e assume "e\<in>{e. admitted adm e}"
  show "initial (inverted e)=terminal e" by (cases e) auto
next
  fix e assume "e\<in>{e. admitted adm e}"
  show "terminal (inverted e)=initial e" by (cases e) auto
next
  fix e assume "e\<in>{e. admitted adm e}"
  show "inverted (inverted e)=e" by (cases e) auto
next
  fix e p q assume "e\<in>{e. admitted adm e}" and pq: "cmp_act D f tr e p q"
  show "p\<in>regions D f (initial e) \<and> q\<in>regions D f (terminal e)" by (rule atom_type[OF pq])
next
  fix e p q r assume "e\<in>{e. admitted adm e}" and "cmp_act D f tr e p q" and "cmp_act D f tr e p r"
  then show "q=r" using atom_functional by auto
next
  fix e p q assume "e\<in>{e. admitted adm e}"
  show "cmp_act D f tr (inverted e) q p = cmp_act D f tr e p q" by (rule atom_inverse)
qed

lemma append_length: "length (p@q) = length p + length q" by simp

lemma source_edge_recovery:
  "source_atom e \<Longrightarrow> cmp_act D f tr e a b \<Longrightarrow> recover_tag a = recover_tag b"
proof -
  have rec: "\<And>u s. s\<in>D u \<Longrightarrow> recovery D f u (f u s)=s"
    using recover_arrival[where D=D and f=f] local_inj by blast
  assume "source_atom e" and "cmp_act D f tr e a b"
  then show ?thesis by (cases e; cases a; cases b)
    (auto simp: recover_tag_def src_graph_def src_match_def rec)
qed

lemma source_sequence_recovery:
  "source_only es \<Longrightarrow> sequence (cmp_act D f tr) es a b \<Longrightarrow> recover_tag a = recover_tag b"
proof (induction es arbitrary: a)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  then obtain c where edge: "cmp_act D f tr e a c" and rest: "sequence (cmp_act D f tr) es c b" by auto
  have se: "source_atom e" and ss: "source_only es" using Cons.prems(1) unfolding source_only_def by auto
  have "recover_tag a = recover_tag c" by (rule source_edge_recovery[OF se edge])
  also have "... = recover_tag b" by (rule Cons.IH[OF ss rest])
  finally show ?case .
qed

theorem source_path_preserves_recovery:
  "source_only es \<Longrightarrow> W.action u es v a b \<Longrightarrow> recover_tag a = recover_tag b"
  unfolding W.action_def using source_sequence_recovery by blast

theorem source_loop_identity:
  assumes so: "source_only es" and run: "W.action u es u a b"
  shows "a=b"
proof -
  have ay: "a\<in>regions D f u" and by_mem: "b\<in>regions D f u"
    using run W.sequence_end unfolding W.action_def by blast+
  have fa: "fst a=u" and fb: "fst b=u" and sa: "snd a\<in>f u ` D u" and sb: "snd b\<in>f u ` D u"
    using ay by_mem unfolding regions_def by auto
  have eq: "recovery D f u (snd a) = recovery D f u (snd b)"
    using source_path_preserves_recovery[OF so run] unfolding recover_tag_def using fa fb by simp
  have ar: "f u (recovery D f u (snd a)) = snd a" by (rule arrival_recovery[where D=D and f=f and u=u and a="snd a", OF sa])
  have br: "f u (recovery D f u (snd b)) = snd b" by (rule arrival_recovery[where D=D and f=f and u=u and a="snd b", OF sb])
  have applied: "f u (recovery D f u (snd a)) = f u (recovery D f u (snd b))"
    by (rule arg_cong[where f="f u", OF eq])
  have "snd a=snd b" by (rule trans[OF sym[OF ar] trans[OF applied br]])
  then show ?thesis using fa fb by (cases a; cases b) auto
qed

theorem delete_source_loop_action:
  assumes p: "W.typed u p v" and lp: "W.typed v loop v" and q: "W.typed v q w"
    and so: "source_only loop" and run: "W.action u ((p@loop)@q) w a b"
  shows "W.action u (p@q) w a b"
proof -
  have pl: "W.typed u (p@loop) v" using p lp W.typed_append by blast
  obtain c where left: "W.action u (p@loop) v a c" and right: "W.action v q w c b"
    using W.action_append[OF pl q] run by blast
  obtain x where px: "W.action u p v a x" and lx: "W.action v loop v x c"
    using W.action_append[OF p lp] left by blast
  have "x=c" by (rule source_loop_identity[OF so lx])
  then show ?thesis using W.action_append[OF p q] px right by blast
qed

inductive delete_loop :: "'u \<Rightarrow> 'u \<Rightarrow> 'u comparison_atom list \<Rightarrow> 'u comparison_atom list \<Rightarrow> bool" where
  segment: "W.typed u p v \<Longrightarrow> W.typed v loop v \<Longrightarrow> W.typed v q w \<Longrightarrow>
    source_only loop \<Longrightarrow> 0 < length loop \<Longrightarrow> delete_loop u w ((p@loop)@q) (p@q)"

theorem deletion_strictly_shortens:
  "delete_loop u v p q \<Longrightarrow> length q < length p"
  by (erule delete_loop.cases) auto

theorem deletion_extends_action:
  "delete_loop u v p q \<Longrightarrow> W.action u p v a b \<Longrightarrow> W.action u q v a b"
  by (erule delete_loop.cases) (blast intro: delete_source_loop_action)

theorem deletion_extends_domain:
  "delete_loop u v p q \<Longrightarrow> (\<exists>b. W.action u p v a b) \<Longrightarrow> (\<exists>b. W.action u q v a b)"
  using deletion_extends_action by blast

theorem deletion_exact_on_old_domain:
  assumes del: "delete_loop u v p q" and dom: "\<exists>c. W.action u p v a c"
  shows "W.action u q v a b = W.action u p v a b"
proof
  assume qb: "W.action u q v a b"
  obtain c where pc: "W.action u p v a c" using dom by blast
  have qc: "W.action u q v a c" by (rule deletion_extends_action[OF del pc])
  have "c=b" by (rule W.action_functional[OF qc qb])
  then show "W.action u p v a b" using pc by simp
next
  assume "W.action u p v a b"
  then show "W.action u q v a b" by (rule deletion_extends_action[OF del])
qed

inductive source_reduction :: "'u \<Rightarrow> 'u \<Rightarrow> 'u comparison_atom list \<Rightarrow> 'u comparison_atom list \<Rightarrow> bool" where
  refl: "source_reduction u v p p" |
  step: "delete_loop u v p q \<Longrightarrow> source_reduction u v q r \<Longrightarrow> source_reduction u v p r"
definition irreducible where "irreducible u v p = (\<not>(\<exists>q. delete_loop u v p q))"

theorem finite_source_reduction:
  "\<exists>q. source_reduction u v p q \<and> irreducible u v q"
proof (induction p rule: measure_induct_rule[of length])
  case (less p)
  show ?case
  proof (cases "irreducible u v p")
    case True
    then show ?thesis using source_reduction.refl by blast
  next
    case False
    then obtain q where del: "delete_loop u v p q" unfolding irreducible_def by blast
    have shorter: "length q < length p" by (rule deletion_strictly_shortens[OF del])
    obtain r where red: "source_reduction u v q r" and terminal: "irreducible u v r"
      using less.IH[OF shorter] by blast
    have "source_reduction u v p r" by (rule source_reduction.step[OF del red])
    then show ?thesis using terminal by blast
  qed
qed

theorem reduction_extends_action:
  "source_reduction u v p q \<Longrightarrow> W.action u p v a b \<Longrightarrow> W.action u q v a b"
  by (induction rule: source_reduction.induct) (auto intro: deletion_extends_action)

theorem reduction_exact_on_old_domain:
  assumes red: "source_reduction u v p q" and dom: "\<exists>c. W.action u p v a c"
  shows "W.action u q v a b = W.action u p v a b"
proof
  assume qb: "W.action u q v a b"
  obtain c where pc: "W.action u p v a c" using dom by blast
  have qc: "W.action u q v a c" by (rule reduction_extends_action[OF red pc])
  have "c=b" by (rule W.action_functional[OF qc qb])
  then show "W.action u p v a b" using pc by simp
next
  assume "W.action u p v a b"
  then show "W.action u q v a b" by (rule reduction_extends_action[OF red])
qed

definition pure_loop_identity where
  "pure_loop_identity = (\<forall>u es a b. transport_only es \<longrightarrow> W.action u es u a b \<longrightarrow> a=b)"
definition irreducible_mixed_identity where
  "irreducible_mixed_identity = (\<forall>u es a b. irreducible u u es \<longrightarrow> \<not>source_only es \<longrightarrow>
    \<not>transport_only es \<longrightarrow> W.action u es u a b \<longrightarrow> a=b)"

theorem pure_and_irreducible_mixed_give_all_loops:
  assumes pure: "pure_loop_identity" and mixed: "irreducible_mixed_identity"
  shows W.loop_identity
proof (unfold W.loop_identity_def, intro allI impI)
  fix u p a b
  assume run: "W.action u p u a b"
  obtain q where red: "source_reduction u u p q" and terminal: "irreducible u u q"
    using finite_source_reduction[where u=u and v=u and p=p] by blast
  have rq: "W.action u q u a b" by (rule reduction_extends_action[OF red run])
  show "a=b"
  proof (cases "source_only q")
    case True
    show ?thesis by (rule source_loop_identity[OF True rq])
  next
    case False
    then show ?thesis using pure mixed terminal rq
      unfolding pure_loop_identity_def irreducible_mixed_identity_def by blast
  qed
qed

theorem pure_iff_all_loops_under_mixed:
  "irreducible_mixed_identity \<Longrightarrow> pure_loop_identity = W.loop_identity"
  using pure_and_irreducible_mixed_give_all_loops
  unfolding W.loop_identity_def pure_loop_identity_def by blast

theorem gluing_iff_local_injectivity:
  "irreducible_mixed_identity \<Longrightarrow>
    pure_loop_identity = (\<forall>u. inj_on (\<lambda>p. {(x,y). W.orbit x y}``{p}) (regions D f u))"
  using pure_iff_all_loops_under_mixed comparison_loop_projection_criterion by blast

end

ML \<open>
val roots = @{thms native_comparison.append_length native_comparison.source_path_preserves_recovery
  native_comparison.source_loop_identity native_comparison.delete_source_loop_action
  native_comparison.deletion_strictly_shortens native_comparison.deletion_extends_action
  native_comparison.deletion_extends_domain native_comparison.deletion_exact_on_old_domain
  native_comparison.finite_source_reduction native_comparison.reduction_extends_action
  native_comparison.reduction_exact_on_old_domain native_comparison.pure_and_irreducible_mixed_give_all_loops
  native_comparison.pure_iff_all_loops_under_mixed native_comparison.gluing_iff_local_injectivity};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
