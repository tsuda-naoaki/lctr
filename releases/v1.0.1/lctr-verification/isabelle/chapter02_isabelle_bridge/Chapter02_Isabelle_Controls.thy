theory Chapter02_Isabelle_Controls
  imports Chapter02_Isabelle_Bridge
begin

definition tiny_assignment :: "bool \<Rightarrow> unit" where
  "tiny_assignment z = ()"

definition tiny_label :: "unit \<Rightarrow> role \<Rightarrow> unit" where
  "tiny_label d r = ()"

lemma empty_admissible_index:
  "ri_family tiny_assignment tiny_label {} = {}"
  by (simp add: ri_family_def)

lemma four_role_positions_are_distinct:
  "distinct
    [ri_role (bundle_clock (role_bundle tiny_assignment tiny_label z)),
     ri_role (bundle_detector (role_bundle tiny_assignment tiny_label z)),
     ri_role (bundle_body (role_bundle tiny_assignment tiny_label z)),
     ri_role (bundle_observer (role_bundle tiny_assignment tiny_label z))]"
  by (simp add: role_bundle_def role_instance_def)

lemma noninjective_assignment_same_specified_data:
  "tiny_assignment True = tiny_assignment False"
  by (simp add: tiny_assignment_def)

lemma noninjective_assignment_indices_still_distinct_in_every_role:
  "role_instance tiny_assignment tiny_label r True
   \<noteq> role_instance tiny_assignment tiny_label r False"
  by (simp add: role_instance_def tiny_assignment_def tiny_label_def)

lemma noninjective_assignment_refutes_erased_index_identity:
  "\<not> (\<forall>z1 z2.
       tiny_assignment z1 = tiny_assignment z2 \<longrightarrow>
       role_instance tiny_assignment tiny_label Clock z1
       = role_instance tiny_assignment tiny_label Clock z2)"
proof
  assume h: "\<forall>z1 z2. tiny_assignment z1 = tiny_assignment z2 \<longrightarrow> role_instance tiny_assignment tiny_label Clock z1 = role_instance tiny_assignment tiny_label Clock z2"
  have ha: "tiny_assignment True = tiny_assignment False"
    by (simp add: tiny_assignment_def)
  have hri:
    "role_instance tiny_assignment tiny_label Clock True
     = role_instance tiny_assignment tiny_label Clock False"
    using h ha by blast
  have "True = False"
    using hri by (simp add: role_instance_def)
  then show False by simp
qed

lemma concrete_realization_domain_excludes_body:
  "\<forall>ri \<in> realization_input tiny_assignment tiny_label UNIV.
     ri_role ri \<noteq> Body"
  using realization_input_excludes_body by blast

lemma body_in_realization_domain_is_impossible:
  "\<not> (\<exists>ri \<in> realization_input tiny_assignment tiny_label UNIV.
       ri_role ri = Body)"
  using realization_input_excludes_body by blast

end
