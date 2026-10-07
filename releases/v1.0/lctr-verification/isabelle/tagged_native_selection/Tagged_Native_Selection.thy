theory Tagged_Native_Selection
  imports "LCTR_Tagged_Native_Law_Family.Tagged_Native_Law_Family"
    "LCTR_Native_Law_Datum_Semantics.Native_Law_Datum_Semantics"
begin

definition tagged_family where
  "tagged_family d b=law_index_encoding.encoded
    (field_embed b ` law_indices d) (field_project b)
    (full_family_encoding.encoded (time_carrier d)
      (field_embed b ` time_carrier d) (field_embed b) (field_project b) d
      (\<lambda>a. field_embed(b,a) ` input_carrier d a)
      (\<lambda>a. field_embed(b,a) ` output_carrier d a)
      (\<lambda>a. field_embed(b,a)) (\<lambda>a. field_project(b,a))
      (\<lambda>a. field_embed(b,a)) (\<lambda>a. field_project(b,a)))"

context tagged_native_family
begin
lemma tagged_family_exact: "tagged_family d b=encoded_family"
  by (simp only: tagged_family_def)
end

lemma tagged_condition:
  assumes wf: "well_typed_family d"
  shows "Core_Native_Law_Family.condition (tagged_family d b) i=
    Core_Native_Law_Family.condition d i"
proof -
  interpret tagged_native_family d b by (unfold_locales; rule wf)
  show ?thesis by (cases i; simp only: tagged_family_exact
    Core_Native_Law_Family.condition.simps condition1 condition2 condition3 condition4 condition5)
qed

lemma tagged_all_conditions:
  assumes wf: "well_typed_family d"
  shows "Core_Native_Law_Family.all_conditions (tagged_family d b)=
    Core_Native_Law_Family.all_conditions d"
proof -
  interpret tagged_native_family d b by (unfold_locales; rule wf)
  show ?thesis by (simp only: tagged_family_exact all_conditions_preserved)
qed

lemma tagged_well_typed:
  assumes wf: "well_typed_family d"
  shows "well_typed_family (tagged_family d b)"
proof -
  interpret tagged_native_family d b by (unfold_locales; rule wf)
  show ?thesis by (simp only: tagged_family_exact; rule encoded_well_typed)
qed

definition tagged_datum where
  "tagged_datum d b=\<lparr>eval_spec=eval_spec d, family=tagged_family (family d) b\<rparr>"
definition tagged_selection where
  "tagged_selection selection e=map_option (\<lambda>d. tagged_datum d e) (selection e)"

lemma tagged_spec_exact: "eval_spec(tagged_datum d b)=eval_spec d"
  by (simp add: tagged_datum_def)
lemma tagged_domain_exact:
  "tagged_selection selection e=None \<longleftrightarrow> selection e=None"
  by (simp add: tagged_selection_def)
lemma tagged_selection_some:
  "selection e=Some d \<Longrightarrow> tagged_selection selection e=Some(tagged_datum d e)"
  by (simp add: tagged_selection_def)

lemma tagged_operative:
  assumes wf: "well_typed_family (family d)"
  shows "native_law_operative dyn joint (tagged_datum d b)=native_law_operative dyn joint d"
  by (simp only: native_law_operative_def tagged_datum_def law_datum.select_convs
    tagged_all_conditions[OF wf])

lemma tagged_total_condition:
  assumes wf: "\<And>d. selection e=Some d \<Longrightarrow> well_typed_family (family d)"
  shows "native_total_condition (tagged_selection selection) e i=
    native_total_condition selection e i"
proof (cases "selection e")
  case None
  then show ?thesis by (simp add: native_total_condition_def tagged_selection_def)
next
  case (Some d)
  have wd: "well_typed_family (family d)" by (rule wf[OF Some])
  show ?thesis by (simp add: native_total_condition_def tagged_selection_def Some
    tagged_datum_def tagged_condition[OF wd])
qed

lemma tagged_failure:
  assumes wf: "\<And>d. selection e=Some d \<Longrightarrow> well_typed_family (family d)"
  shows "native_selected_failure (tagged_selection selection) e=
    native_selected_failure selection e"
  by (simp only: native_selected_failure_def tagged_domain_exact tagged_total_condition[OF wf])

context ready_native_selection
begin

lemma tagged_selection_ready: "ready_native_selection (tagged_selection selection) dyn"
proof (unfold_locales)
  fix e d assume h: "tagged_selection selection e=Some d"
  obtain old where old: "selection e=Some old" "d=tagged_datum old e"
    using h unfolding tagged_selection_def by (cases "selection e") auto
  show "dyn e" by (rule domain_ready[OF old(1)])
next
  fix e d assume h: "tagged_selection selection e=Some d"
  obtain old where old: "selection e=Some old" "d=tagged_datum old e"
    using h unfolding tagged_selection_def by (cases "selection e") auto
  show "eval_spec d=Inl e" using same_spec[OF old(1)] by (simp only: old(2) tagged_spec_exact)
qed

end

ML \<open>
val roots = @{thms tagged_native_family.tagged_family_exact tagged_condition
 tagged_all_conditions tagged_well_typed tagged_spec_exact tagged_domain_exact
 tagged_selection_some tagged_operative tagged_total_condition tagged_failure
 ready_native_selection.tagged_selection_ready};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
