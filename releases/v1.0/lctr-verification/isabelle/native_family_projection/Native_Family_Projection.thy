theory Native_Family_Projection
  imports "LCTR_Native_Family_Conditions.Native_Family_Conditions"
begin

record ('r,'j) native_condition_components =
  nf_atlas :: "'r \<Rightarrow> 'j \<Rightarrow> bool"
  nf_jet :: "'r \<Rightarrow> 'j \<Rightarrow> bool"
  nf_member :: "'r \<Rightarrow> 'j \<Rightarrow> bool"
  nf_value :: "'r \<Rightarrow> 'j \<Rightarrow> bool"
  nf_time :: "'r \<Rightarrow> 'r \<Rightarrow> 'j \<Rightarrow> bool"

definition family_first where "family_first Reps Selected p \<longleftrightarrow>
  (\<forall>rho\<in>Reps. \<forall>j\<in>Selected. nf_atlas p rho j)"
definition family_second where "family_second Reps Selected p \<longleftrightarrow>
  (\<forall>rho\<in>Reps. \<forall>j\<in>Selected. nf_jet p rho j)"
definition family_third where "family_third Reps Selected p \<longleftrightarrow>
  (\<forall>rho\<in>Reps. \<forall>j\<in>Selected. nf_member p rho j)"
definition family_fourth where "family_fourth Reps Selected p \<longleftrightarrow>
  (\<forall>rho\<in>Reps. \<forall>j\<in>Selected. nf_value p rho j)"
definition family_fifth where "family_fifth Reps Selected p \<longleftrightarrow>
  (\<forall>rho\<in>Reps. \<forall>other\<in>Reps.
    (\<forall>j\<in>Selected. nf_atlas p rho j) \<and>
    (\<forall>j\<in>Selected. nf_atlas p other j) \<and>
    (\<forall>j\<in>Selected. nf_time p rho other j))"
definition family_complete where "family_complete Reps Selected p \<longleftrightarrow>
  family_first Reps Selected p \<and> family_second Reps Selected p \<and>
  family_third Reps Selected p \<and> family_fourth Reps Selected p \<and> family_fifth Reps Selected p"

definition component_complete where "component_complete Reps p j \<longleftrightarrow>
  (\<forall>rho\<in>Reps. nf_atlas p rho j) \<and> (\<forall>rho\<in>Reps. nf_jet p rho j) \<and>
  (\<forall>rho\<in>Reps. nf_member p rho j) \<and> (\<forall>rho\<in>Reps. nf_value p rho j) \<and>
  (\<forall>rho\<in>Reps. \<forall>other\<in>Reps. nf_atlas p rho j \<and> nf_atlas p other j \<and> nf_time p rho other j)"

lemma family_assembly_exact:
  "family_complete Reps Selected p \<longleftrightarrow> (\<forall>j\<in>Selected. component_complete Reps p j)"
  by (auto simp: family_complete_def family_first_def family_second_def family_third_def
    family_fourth_def family_fifth_def component_complete_def)

lemma family_third_requires_second:
  "(\<And>rho j. rho\<in>Reps \<Longrightarrow> j\<in>Selected \<Longrightarrow>
    nf_member p rho j \<Longrightarrow> nf_jet p rho j) \<Longrightarrow>
    family_third Reps Selected p \<Longrightarrow> family_second Reps Selected p"
  by (auto simp: family_third_def family_second_def)

lemma family_fourth_requires_first:
  "(\<And>rho j. rho\<in>Reps \<Longrightarrow> j\<in>Selected \<Longrightarrow>
    nf_value p rho j \<Longrightarrow> nf_atlas p rho j) \<Longrightarrow>
    family_fourth Reps Selected p \<Longrightarrow> family_first Reps Selected p"
  by (auto simp: family_fourth_def family_first_def)

context native_family_component_atlas
begin
definition component_projection :: "((('c set set \<Rightarrow> real) \<Rightarrow>
    'ti \<Rightarrow> ('bi \<times> 'bo) \<Rightarrow> (real \<times> (nat \<Rightarrow> 'e \<times> 'f)) set)) \<Rightarrow>
    (('c set set \<Rightarrow> real),unit) native_condition_components" where
  "component_projection Rel =
    \<lparr>nf_atlas = (\<lambda>rho _. AtlasAt rho),
     nf_jet = (\<lambda>rho _. JetAt rho),
     nf_member = (\<lambda>rho _. JetAt rho \<and> MemberAt rho (Rel rho)),
     nf_value = (\<lambda>rho _. ValueAt rho (Rel rho)),
     nf_time = (\<lambda>rho other _. TimeAt rho other (Rel rho) (Rel other))\<rparr>"

lemma first_projection_exact:
  "family_first Reps UNIV (component_projection Rel) \<longleftrightarrow> C1"
  by (simp add: family_first_def component_projection_def C1_def)
lemma second_projection_exact:
  "family_second Reps UNIV (component_projection Rel) \<longleftrightarrow> C2"
  by (simp add: family_second_def component_projection_def C2_def)
lemma third_projection_exact:
  "family_third Reps UNIV (component_projection Rel) \<longleftrightarrow> C3 Rel"
  by (simp add: family_third_def component_projection_def C3_def)
lemma fourth_projection_exact:
  "family_fourth Reps UNIV (component_projection Rel) \<longleftrightarrow> C4 Rel"
  by (simp add: family_fourth_def component_projection_def fourth_condition_exact)
lemma fifth_projection_exact:
  "family_fifth Reps UNIV (component_projection Rel) \<longleftrightarrow> C5 Rel"
  by (simp add: family_fifth_def component_projection_def C5_def)
lemma complete_projection_exact:
  "family_complete Reps UNIV (component_projection Rel) \<longleftrightarrow> Complete Rel"
  by (simp add: family_complete_def Complete_def first_projection_exact second_projection_exact
    third_projection_exact fourth_projection_exact fifth_projection_exact)

lemma component_member_keeps_jet:
  "nf_member (component_projection Rel) rho j \<Longrightarrow> nf_jet (component_projection Rel) rho j"
  by (simp add: component_projection_def)
lemma component_value_keeps_atlas:
  "rho\<in>Reps \<Longrightarrow> nf_value (component_projection Rel) rho j \<Longrightarrow>
    nf_atlas (component_projection Rel) rho j"
  by (simp add: component_projection_def; rule fourth_at_actual)
end

ML \<open>
val roots = @{thms family_assembly_exact family_third_requires_second family_fourth_requires_first
  native_family_component_atlas.first_projection_exact native_family_component_atlas.second_projection_exact
  native_family_component_atlas.third_projection_exact native_family_component_atlas.fourth_projection_exact
  native_family_component_atlas.fifth_projection_exact native_family_component_atlas.complete_projection_exact
  native_family_component_atlas.component_member_keeps_jet native_family_component_atlas.component_value_keeps_atlas};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
