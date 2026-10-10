theory Core_Differential_Refinement
  imports LCTR_Core_Differential_Output.Core_Differential_Output
    LCTR_Core_Refinement_Forest.Core_Refinement_Forest
begin

context matching_differential
begin
lemma parent_source_exact:
  "parent S i={ev\<in>S. nativeFailure ev \<and> nativeMinimal ev i}"
  using native_failure_cover by (auto simp: parent_def)
lemma parent_subset_evaluation: "parent S i\<subseteq>S"
  by (auto simp: parent_def)
lemma parent_requires_selection: "parent S i\<subseteq>diffDomain"
  by (auto simp: parent_def nativeMinimal_def nativeLawReady_def inputRelation_def)
lemma parents_cover: "(\<Union>i. parent S i)={ev\<in>S. nativeFailure ev}"
  using native_failure_cover by (auto simp: parent_def)
end

locale differential_refinement = matching_differential lawDomain lawDatum diffDomain structureAt operative
  for lawDomain :: "'e set" and lawDatum :: "'e\<Rightarrow>'law" and diffDomain :: "'e set"
    and structureAt :: "'e\<Rightarrow>'o native" and operative :: "'law\<Rightarrow>bool" +
  fixes S :: "'e set" and J :: "Core_Differential_Failure.node\<Rightarrow>'j set"
    and K :: "Core_Differential_Failure.node\<Rightarrow>'j\<Rightarrow>'k set"
    and first :: "Core_Differential_Failure.node\<Rightarrow>'j\<Rightarrow>'e set"
    and second :: "Core_Differential_Failure.node\<Rightarrow>'j\<Rightarrow>'k\<Rightarrow>'e set"
  assumes first_sub: "\<And>i j. j\<in>J i \<Longrightarrow> first i j\<subseteq>parent S i"
    and second_sub: "\<And>i j k. j\<in>J i \<Longrightarrow> k\<in>K i j \<Longrightarrow> second i j k\<subseteq>first i j"
begin

sublocale R: two_level_regions UNIV J K "parent S" first second
  by unfold_locales (auto dest: first_sub[THEN subsetD] second_sub[THEN subsetD])

lemma child_and_remainder_typing:
  "j\<in>J i \<Longrightarrow> first i j\<subseteq>parent S i \<and> R.F.unrefined (Root i)\<subseteq>parent S i"
  using first_sub by (auto simp: R.F.unrefined_def)

lemmas all_node_decompositions = R.F.node_decomposition
lemmas conditional_disjoint_children = R.F.child_family_with_remainder
lemmas ancestor_region_inclusion = R.F.ancestor_inclusion
lemmas second_level_terminal = R.two_level_leaf

lemma root_split_exact:
  "R.F.covered (Root i)=(\<Union>j\<in>J i. first i j) \<and>
    R.F.unrefined (Root i)=parent S i-(\<Union>j\<in>J i. first i j)"
  by (simp add: R.F.covered_def R.F.unrefined_def)
lemma first_split_exact:
  "j\<in>J i \<Longrightarrow> R.F.covered (First i j)=(\<Union>k\<in>K i j. second i j k) \<and>
    R.F.unrefined (First i j)=first i j-(\<Union>k\<in>K i j. second i j k)"
  by (simp add: R.F.covered_def R.F.unrefined_def)

lemma root_snapshot_monotonicity:
  fixes embed :: "'j0\<Rightarrow>'j1" and r0 :: "'j0\<Rightarrow>'e set" and r1 :: "'j1\<Rightarrow>'e set"
  assumes maps: "\<And>j. j\<in>J0 \<Longrightarrow> embed j\<in>J1"
    and same: "\<And>j. j\<in>J0 \<Longrightarrow> r0 j=r1 (embed j)"
  shows "(\<Union>j\<in>J0. r0 j)\<subseteq>(\<Union>j\<in>J1. r1 j) \<and>
    parent S i-(\<Union>j\<in>J1. r1 j)\<subseteq>parent S i-(\<Union>j\<in>J0. r0 j)"
  by (rule snapshot_monotonicity[where I=J0 and J=J1 and r=r0 and s=r1 and embed=embed
    and P="parent S i", OF maps same])

end
ML \<open>
val roots = @{thms matching_differential.parent_source_exact matching_differential.parent_subset_evaluation
  matching_differential.parent_requires_selection matching_differential.parents_cover
  differential_refinement.child_and_remainder_typing differential_refinement.all_node_decompositions
  differential_refinement.conditional_disjoint_children differential_refinement.ancestor_region_inclusion
  differential_refinement.second_level_terminal differential_refinement.root_split_exact
  differential_refinement.first_split_exact differential_refinement.root_snapshot_monotonicity};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
