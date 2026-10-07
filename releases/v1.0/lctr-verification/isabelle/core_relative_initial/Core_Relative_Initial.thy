theory Core_Relative_Initial
  imports Main
begin

definition initial where
  "initial A r I = (\<forall>x\<in>A. \<forall>y\<in>I. r x y \<longrightarrow> x\<in>I)"
definition family where "family A V r = {I. I\<subseteq>V \<and> initial A r I}"
definition greatest where "greatest F I = (I\<in>F \<and> (\<forall>J\<in>F. J\<subseteq>I))"
definition endpoint where "endpoint r I a = (a\<in>I \<and> (\<forall>x\<in>I. r x a))"

lemma empty_initial: "{}\<in>family A V r"
  by (auto simp: family_def initial_def)
lemma union_initial: "\<Union>(family A V r)\<in>family A V r"
  unfolding family_def initial_def by blast
lemma union_greatest: "greatest (family A V r) (\<Union>(family A V r))"
  using union_initial unfolding greatest_def by blast
lemma mono_identifies:
  "initial A r V \<Longrightarrow> \<Union>(family A V r) = V"
  using union_greatest unfolding greatest_def family_def by blast
lemma maximum_unique:
  "greatest F I \<Longrightarrow> greatest F J \<Longrightarrow> I=J"
  unfolding greatest_def by auto
lemma endpoint_characterization:
  "(\<exists>a. endpoint r I a) = (\<exists>a\<in>I. \<forall>x\<in>I. r x a)"
  by (auto simp: endpoint_def)

ML \<open>
val roots = @{thms empty_initial union_initial union_greatest mono_identifies
  maximum_unique endpoint_characterization};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int (length roots));
\<close>
end
