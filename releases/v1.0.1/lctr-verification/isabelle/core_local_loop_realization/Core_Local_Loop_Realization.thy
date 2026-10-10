theory Core_Local_Loop_Realization
 imports "LCTR_Core_Source_Loops.Core_Source_Loops"
begin

record ('u,'v) loop_spec =
 base :: 'u
 word :: "'u comparison_atom list"
 specified :: "('u\<times>'v) set"

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

definition valid_spec where
 "valid_spec s = (W.typed (base s) (word s) (base s) \<and> transport_only(word s) \<and>
   specified s\<subseteq>regions D f (base s))"
definition realizable where
 "realizable s = (\<forall>a\<in>specified s. \<exists>b. W.action(base s)(word s)(base s)a b)"
definition realize where
 "realize s a = (SOME b. W.action(base s)(word s)(base s)a b)"
definition id_on_specified where
 "id_on_specified s = (\<forall>a\<in>specified s. \<forall>b. W.action(base s)(word s)(base s)a b \<longrightarrow> a=b)"
definition restrict_spec where "restrict_spec s domain=s\<lparr>specified:=domain\<rparr>"

theorem realization_correct:
 "realizable s \<Longrightarrow> a\<in>specified s \<Longrightarrow> W.action(base s)(word s)(base s)a(realize s a)"
 unfolding realizable_def realize_def by (rule someI_ex) blast

theorem realization_graph:
 assumes real: "realizable s" and a: "a\<in>specified s"
 shows "realize s a=b \<longleftrightarrow> W.action(base s)(word s)(base s)a b"
 using realization_correct[OF real a] W.action_functional by blast

theorem realization_injective:
 assumes real: "realizable s"
 shows "inj_on (realize s) (specified s)"
proof (rule inj_onI)
 fix a b assume a: "a\<in>specified s" and b: "b\<in>specified s" and eq: "realize s a=realize s b"
 have ar: "W.action(base s)(word s)(base s)a(realize s b)"
  using realization_correct[OF real a] by (simp only: eq)
 have br: "W.action(base s)(word s)(base s)b(realize s b)" by (rule realization_correct[OF real b])
 show "a=b" by (rule W.action_injective[OF ar br])
qed

theorem realization_unique:
 assumes real: "realizable s" and correct: "\<And>a. a\<in>specified s \<Longrightarrow> W.action(base s)(word s)(base s)a(g a)"
 shows "\<forall>a\<in>specified s. g a=realize s a"
proof (intro ballI)
 fix a assume a: "a\<in>specified s"
 have given: "W.action(base s)(word s)(base s)a(g a)" by (rule correct[OF a])
 have chosen: "W.action(base s)(word s)(base s)a(realize s a)" by (rule realization_correct[OF real a])
 show "g a=realize s a" by (rule W.action_functional[OF given chosen])
qed

theorem realizable_iff_total_realization:
 "realizable s \<longleftrightarrow> (\<exists>g. (\<forall>a\<in>specified s. g a\<in>regions D f (base s)) \<and>
   (\<forall>a\<in>specified s. W.action(base s)(word s)(base s)a(g a)))"
proof
 assume h: "realizable s"
 have correct: "\<And>a. a\<in>specified s \<Longrightarrow> W.action(base s)(word s)(base s)a(realize s a)"
  by (rule realization_correct[OF h])
 have typed: "\<And>a. a\<in>specified s \<Longrightarrow> realize s a\<in>regions D f(base s)"
  using correct W.sequence_end unfolding W.action_def by blast
 show "\<exists>g. (\<forall>a\<in>specified s. g a\<in>regions D f (base s)) \<and>
   (\<forall>a\<in>specified s. W.action(base s)(word s)(base s)a(g a))"
  using correct typed by blast
next
 assume "\<exists>g. (\<forall>a\<in>specified s. g a\<in>regions D f (base s)) \<and>
   (\<forall>a\<in>specified s. W.action(base s)(word s)(base s)a(g a))"
 then show "realizable s" unfolding realizable_def by blast
qed

theorem specified_identity_iff:
 "realizable s \<Longrightarrow> (id_on_specified s \<longleftrightarrow> (\<forall>a\<in>specified s. realize s a=a))"
 using realization_correct realization_graph unfolding id_on_specified_def by metis

theorem global_identity_restricts:
 "pure_loop_identity \<Longrightarrow> valid_spec s \<Longrightarrow> id_on_specified s"
 unfolding pure_loop_identity_def valid_spec_def id_on_specified_def by blast

theorem restriction_realizable:
 "realizable s \<Longrightarrow> domain\<subseteq>specified s \<Longrightarrow> realizable(restrict_spec s domain)"
 unfolding realizable_def restrict_spec_def by auto

theorem restriction_agrees:
 "realize(restrict_spec s domain)a=realize s a"
 by (simp add: realize_def restrict_spec_def)

theorem empty_specification:
 "realizable(restrict_spec s {}) \<and> id_on_specified(restrict_spec s {})"
 by (simp add: realizable_def id_on_specified_def restrict_spec_def)

lemma forward_action:
 "adm u v \<Longrightarrow> a\<in>f u ` D u \<Longrightarrow> b\<in>f v ` D v \<Longrightarrow> tr u v a b \<Longrightarrow>
  W.action u [Forward u v] v (u,a) (v,b)"
 by (auto simp: W.action_def regions_def)

lemma empty_forward_spec_valid:
 "adm u u \<Longrightarrow> valid_spec \<lparr>base=u,word=[Forward u u],specified={}\<rparr>"
 by (simp add: valid_spec_def transport_only_def)

end

interpretation Flip: native_comparison "\<lambda>_::unit. UNIV::bool set" "\<lambda>_. id"
 "\<lambda>_ _. \<lambda>a b::bool. b=(\<not>a)" "\<lambda>_ _. True"
 by standard auto

abbreviation flip_spec :: "(unit,bool) loop_spec" where
 "flip_spec \<equiv> \<lparr>base=(),word=[Forward () ()],specified={}\<rparr>"

lemma control_spec_valid: "Flip.valid_spec flip_spec"
 by (rule Flip.empty_forward_spec_valid) simp

theorem control_path_pure: "transport_only [Forward () ()]"
 by (simp add: transport_only_def)

theorem control_global_identity_fails: "\<not>Flip.pure_loop_identity"
proof
 assume h: "Flip.pure_loop_identity"
 have run: "typed_actions.action (regions (\<lambda>_::unit. UNIV::bool set) (\<lambda>_. id))
  {e. admitted (\<lambda>_ _. True) e} initial terminal (cmp_act (\<lambda>_::unit. UNIV::bool set) (\<lambda>_. id) (\<lambda>_ _. \<lambda>a b::bool. b=(\<not>a)))
  () [Forward () ()] () ((),False) ((),True)"
  by (rule Flip.forward_action) auto
 have "((),False)=((),True)" using h control_path_pure run unfolding Flip.pure_loop_identity_def by blast
 then show False by simp
qed

theorem specified_identity_does_not_imply_global:
 "Flip.realizable flip_spec \<and> Flip.id_on_specified flip_spec \<and> \<not>Flip.pure_loop_identity"
 using control_global_identity_fails by (simp add: Flip.realizable_def Flip.id_on_specified_def)

ML \<open>
val roots = @{thms native_comparison.realization_correct native_comparison.realization_graph
 native_comparison.realization_injective native_comparison.realization_unique
 native_comparison.realizable_iff_total_realization native_comparison.specified_identity_iff
 native_comparison.global_identity_restricts native_comparison.restriction_realizable
 native_comparison.restriction_agrees native_comparison.empty_specification
 control_path_pure control_global_identity_fails specified_identity_does_not_imply_global};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = if null (Thm_Deps.all_oracles @{thms control_spec_valid}) then () else error "Unexpected helper oracle dependency";
\<close>
end
