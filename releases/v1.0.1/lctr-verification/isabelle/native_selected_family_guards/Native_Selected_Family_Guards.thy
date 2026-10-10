theory Native_Selected_Family_Guards
  imports "LCTR_Native_Differential_Synthesis_Alignment.Native_Differential_Synthesis_Alignment"
begin

definition family_failure_input :: "'r set \<Rightarrow> 'j set \<Rightarrow> ('r,'j) native_condition_components \<Rightarrow> 'r native"
  where "family_failure_input Reps Selected p =
    \<lparr>Core_Differential_Failure.native.space = Reps,
     Core_Differential_Failure.native.atlas = (\<lambda>r. \<forall>j\<in>Selected. nf_atlas p r j),
     Core_Differential_Failure.native.jet = (\<lambda>r. \<forall>j\<in>Selected. nf_jet p r j),
     Core_Differential_Failure.native.member = (\<lambda>r. \<forall>j\<in>Selected. nf_member p r j),
     Core_Differential_Failure.native.valueCov = (\<lambda>r. \<forall>j\<in>Selected. nf_value p r j),
     Core_Differential_Failure.native.timeCov = (\<lambda>r s. \<forall>j\<in>Selected. nf_time p r s j)\<rparr>"

lemma family_failure_input_complete:
  "(\<forall>i. Core_Differential_Failure.condition (family_failure_input Reps Selected p) i) \<longleftrightarrow>
    family_complete Reps Selected p"
  by (simp only: Core_Differential_Failure.all_conditions_complete;
    auto simp: family_failure_input_def family_complete_def family_first_def family_second_def
      family_third_def family_fourth_def family_fifth_def)

lemma family_failure_input_condition:
  "Core_Differential_Failure.condition (family_failure_input Reps Selected p) i \<longleftrightarrow>
    (case i of N1 \<Rightarrow> family_first Reps Selected p
      | N2 \<Rightarrow> family_second Reps Selected p
      | N3 \<Rightarrow> family_second Reps Selected p \<and> family_third Reps Selected p
      | N4 \<Rightarrow> family_first Reps Selected p \<and> family_fourth Reps Selected p
      | N5 \<Rightarrow> family_fifth Reps Selected p)"
  by (cases i; auto simp: family_failure_input_def family_first_def family_second_def
    family_third_def family_fourth_def family_fifth_def)

context native_family_component_atlas
begin
definition failure_input where "failure_input Rel = family_failure_input Reps UNIV (component_projection Rel)"

lemma actual_failure_conditions:
  "Core_Differential_Failure.condition (failure_input Rel) i \<longleftrightarrow>
    (case i of N1 \<Rightarrow> C1 | N2 \<Rightarrow> C2 | N3 \<Rightarrow> C3 Rel
      | N4 \<Rightarrow> C4 Rel | N5 \<Rightarrow> C5 Rel)"
  by (cases i; auto simp: failure_input_def family_failure_input_def component_projection_def
    C1_def C2_def C3_def C4_def C5_def)

lemma actual_failure_input_complete:
  "(\<forall>i. Core_Differential_Failure.condition (failure_input Rel) i) \<longleftrightarrow> Complete Rel"
  by (simp only: failure_input_def family_failure_input_complete complete_projection_exact)

lemma actual_failure_counter:
  "Core_Differential_Failure.counter (failure_input Rel) i \<longleftrightarrow>
    \<not> (case i of N1 \<Rightarrow> C1 | N2 \<Rightarrow> C2 | N3 \<Rightarrow> C3 Rel
      | N4 \<Rightarrow> C4 Rel | N5 \<Rightarrow> C5 Rel)"
  by (simp only: Core_Differential_Failure.condition_failure_witness[symmetric] actual_failure_conditions)
end

locale native_family_selection =
  fixes lawDomain diffDomain :: "'ev set"
    and lawDatum :: "'ev \<Rightarrow> 'law" and data :: "'ev \<Rightarrow> 'r native"
    and lawOK :: "'law \<Rightarrow> bool"
  assumes subdomain: "diffDomain \<subseteq> lawDomain"
begin
sublocale bound: selected_differential diffDomain lawDatum data lawOK .
definition differentialInput where "differentialInput ev = (lawDatum ev, data ev)"
definition selectedOperative where
  "selectedOperative ev \<longleftrightarrow> ev\<in>diffDomain \<and> lawOK (lawDatum ev) \<and>
    (\<forall>i. Core_Differential_Failure.condition (data ev) i)"
definition evaluateLaw where "evaluateLaw ev \<longleftrightarrow> ev\<in>lawDomain \<and> lawOK (lawDatum ev)"

lemma selected_law_owned:
  "ev\<in>diffDomain \<Longrightarrow> fst (differentialInput ev) = lawDatum ev"
  by (simp add: differentialInput_def)
lemma selected_differential_owned:
  "ev\<in>diffDomain \<Longrightarrow> snd (differentialInput ev) = data ev"
  by (simp add: differentialInput_def)
lemma operative_on_domain:
  "ev\<in>diffDomain \<Longrightarrow> selectedOperative ev \<longleftrightarrow>
    lawOK (lawDatum ev) \<and> (\<forall>i. Core_Differential_Failure.condition (data ev) i)"
  by (simp add: selectedOperative_def)
lemma operative_requires_same_law:
  "selectedOperative ev \<Longrightarrow> evaluateLaw ev"
  using subdomain by (auto simp: selectedOperative_def evaluateLaw_def)
lemma outside_selection_unformed:
  "ev\<notin>diffDomain \<Longrightarrow> \<not>selectedOperative ev \<and> \<not>bound.failure ev \<and>
    (\<forall>i. \<not>bound.minimalFailure ev i)"
  using bound.outside_selection_no_failure by (simp add: selectedOperative_def)
lemma selected_condition_native:
  "ev\<in>diffDomain \<Longrightarrow> bound.selectedCondition ev i \<longleftrightarrow>
    Core_Differential_Failure.condition (data ev) i"
  by (rule bound.selected_restricts)
lemma selected_failure_exact:
  "ev\<in>diffDomain \<Longrightarrow> bound.failure ev \<longleftrightarrow>
    lawOK (lawDatum ev) \<and> \<not>selectedOperative ev"
  using bound.failure_vs_operative by (simp add: selectedOperative_def)
lemma selected_minimal_counter:
  "ev\<in>diffDomain \<Longrightarrow> bound.minimalFailure ev i \<longleftrightarrow>
    bound.ancestorReady ev i \<and> Core_Differential_Failure.counter (data ev) i"
  by (rule bound.minimal_failure_witness)
lemma selected_failure_cover:
  "bound.failure ev \<longleftrightarrow> (\<exists>i. bound.minimalFailure ev i)"
  by (rule bound.failure_cover)
end

ML \<open>
val roots = @{thms family_failure_input_complete family_failure_input_condition
  native_family_component_atlas.actual_failure_conditions
  native_family_component_atlas.actual_failure_input_complete
  native_family_component_atlas.actual_failure_counter
  native_family_selection.selected_law_owned native_family_selection.selected_differential_owned
  native_family_selection.operative_on_domain native_family_selection.operative_requires_same_law
  native_family_selection.outside_selection_unformed native_family_selection.selected_condition_native
  native_family_selection.selected_failure_exact native_family_selection.selected_minimal_counter
  native_family_selection.selected_failure_cover};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
