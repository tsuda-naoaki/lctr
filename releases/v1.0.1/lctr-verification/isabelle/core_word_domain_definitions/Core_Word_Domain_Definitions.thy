theory Core_Word_Domain_Definitions
 imports "../core_typed_words/Core_Typed_Words"
begin

definition relation_domain where "relation_domain r={x. \<exists>y. r x y}"
definition relation_fix where "relation_fix r={x. r x x}"

lemma fix_subset_domain: "relation_fix r\<subseteq>relation_domain r"
 by (auto simp: relation_fix_def relation_domain_def)

lemma identity_iff_fixed_domain:
 assumes functional: "\<And>x y z. r x y \<Longrightarrow> r x z \<Longrightarrow> y=z"
 shows "relation_fix r=relation_domain r \<longleftrightarrow> (\<forall>x y. r x y \<longrightarrow> y=x)"
 unfolding relation_fix_def relation_domain_def using functional by blast

lemma empty_identity:
 "relation_fix (\<lambda>(_::'x) _. False)=relation_domain (\<lambda>_ _. False)"
 by (simp add: relation_fix_def relation_domain_def)

context typed_actions
begin
lemma loop_identity_exact:
 "loop_identity \<longleftrightarrow> (\<forall>u es. typed u es u \<longrightarrow>
   relation_fix (action u es u)=relation_domain (action u es u))"
proof -
 have eq: "relation_fix (action u es u)=relation_domain (action u es u) \<longleftrightarrow>
   (\<forall>x y. action u es u x y \<longrightarrow> y=x)" for u es
  by (rule identity_iff_fixed_domain) (rule action_functional)
 show ?thesis using eq unfolding loop_identity_def action_def by blast
qed

lemma erased_orbit_word_witness:
 "orbit x y \<longleftrightarrow> (\<exists>u v es. x\<in>Y u \<and> y\<in>Y v \<and>
   typed u es v \<and> sequence act es x y)"
 using sequence_end unfolding orbit_def action_def by blast

lemma erased_orbit_exact_if_disjoint:
 assumes disj: "\<And>i j z. z\<in>Y i \<Longrightarrow> z\<in>Y j \<Longrightarrow> i=j"
 and x: "x\<in>Y i" and y: "y\<in>Y j"
 shows "orbit x y \<longleftrightarrow> (\<exists>es. action i es j x y)"
proof
 assume h: "orbit x y"
 obtain u v es where xu: "x\<in>Y u" and yv: "y\<in>Y v"
 and t: "typed u es v" and a: "sequence act es x y"
  using h erased_orbit_word_witness by blast
 have ui: "u=i" by (rule disj[OF xu x])
 have vj: "v=j" by (rule disj[OF yv y])
 show "\<exists>es. action i es j x y" using xu t a ui vj unfolding action_def by blast
next
 assume "\<exists>es. action i es j x y"
 then show "orbit x y" unfolding orbit_def by blast
qed
end

locale restricted_typed_actions = typed_actions Y Adm src dst dagger act
 for Y::"'u\<Rightarrow>'x set" and Adm::"'e set"
 and src dst::"'e\<Rightarrow>'u" and dagger::"'e\<Rightarrow>'e"
 and act::"'e\<Rightarrow>'x\<Rightarrow>'x\<Rightarrow>bool" +
 fixes P::"'e\<Rightarrow>bool"
 assumes stable: "e\<in>Adm \<Longrightarrow> P e \<Longrightarrow> P(dagger e)"
begin
definition restricted_atoms where "restricted_atoms={e\<in>Adm. P e}"
definition restricted_atom_action where
 "restricted_atom_action e x y \<longleftrightarrow> e\<in>restricted_atoms \<and> act e x y"

lemma restricted_system:
 "typed_actions Y restricted_atoms src dst dagger act"
 by unfold_locales
  (auto simp: restricted_atoms_def act_inv dest: act_type
    intro: inv_adm stable inv_src inv_dst invol act_fun)

lemma restricted_action:
 "e\<in>restricted_atoms \<Longrightarrow> (restricted_atom_action e x y \<longleftrightarrow> act e x y)"
 by (simp add: restricted_atom_action_def)

lemma restricted_inverse:
 assumes e: "e\<in>restricted_atoms"
 shows "dagger e\<in>restricted_atoms \<and> dagger(dagger e)=e \<and>
 src(dagger e)=dst e \<and> dst(dagger e)=src e \<and>
 (\<forall>x y. restricted_atom_action (dagger e) y x \<longleftrightarrow> restricted_atom_action e x y)"
 using e inv_adm stable invol inv_src inv_dst act_inv
 unfolding restricted_atoms_def restricted_atom_action_def by auto
end

ML \<open>
val roots = @{thms fix_subset_domain identity_iff_fixed_domain empty_identity
 typed_actions.loop_identity_exact typed_actions.erased_orbit_word_witness
 typed_actions.erased_orbit_exact_if_disjoint restricted_typed_actions.restricted_action
 restricted_typed_actions.restricted_inverse};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = if null (Thm_Deps.all_oracles @{thms restricted_typed_actions.restricted_system})
 then () else error "Unexpected oracle dependency";
val _ = writeln("LCTR_CHECKED_ROOTS=" ^ string_of_int(length roots));
\<close>
end
