theory Core_Differential_Selected
  imports Core_Differential_Failure
begin

locale matching_differential =
  fixes lawDomain :: "'e set"
    and lawDatum :: "'e \<Rightarrow> 'law"
    and diffDomain :: "'e set"
    and structureAt :: "'e \<Rightarrow> 'o native"
    and operative :: "'law \<Rightarrow> bool"
  assumes subdomain: "diffDomain \<subseteq> lawDomain"
begin

definition inputRelation where
  "inputRelation e p \<longleftrightarrow> e \<in> diffDomain \<and> p = (lawDatum e, structureAt e)"

lemma input_unique:
  "e \<in> diffDomain \<Longrightarrow> \<exists>!p. inputRelation e p"
  by (auto simp: inputRelation_def)
lemma input_same_selected_law:
  "inputRelation e p \<Longrightarrow> e \<in> lawDomain \<and> fst p = lawDatum e \<and> snd p = structureAt e"
  using subdomain by (auto simp: inputRelation_def)
lemma no_input_outside:
  "e \<notin> diffDomain \<Longrightarrow> \<not> inputRelation e p"
  by (simp add: inputRelation_def)

sublocale bound: selected_differential diffDomain lawDatum structureAt operative .

definition nativeCondition where
  "nativeCondition e i \<longleftrightarrow> (\<exists>p. inputRelation e p \<and> condition (snd p) i)"
definition nativeLawReady where
  "nativeLawReady e \<longleftrightarrow> (\<exists>p. inputRelation e p \<and> operative (fst p))"
definition nativeMinimal where
  "nativeMinimal e i \<longleftrightarrow> nativeLawReady e \<and>
    (\<forall>j. ancestor j i \<longrightarrow> nativeCondition e j) \<and> \<not> nativeCondition e i"
definition nativeFailure where
  "nativeFailure e \<longleftrightarrow> nativeLawReady e \<and> \<not> (\<forall>i. nativeCondition e i)"

lemma condition_exact: "nativeCondition e i \<longleftrightarrow> bound.selectedCondition e i"
  by (auto simp: nativeCondition_def inputRelation_def bound.selectedCondition_def)
lemma law_ready_exact: "nativeLawReady e \<longleftrightarrow> bound.lawReady e"
  by (auto simp: nativeLawReady_def inputRelation_def bound.lawReady_def)
lemma minimal_exact: "nativeMinimal e i \<longleftrightarrow> bound.minimalFailure e i"
  by (simp add: nativeMinimal_def bound.minimalFailure_def bound.ancestorReady_def
    condition_exact law_ready_exact)
lemma failure_exact: "nativeFailure e \<longleftrightarrow> bound.failure e"
  by (simp add: nativeFailure_def bound.failure_def condition_exact law_ready_exact)
lemma native_failure_cover: "nativeFailure e \<longleftrightarrow> (\<exists>i. nativeMinimal e i)"
  by (simp add: failure_exact minimal_exact bound.failure_cover)
lemma native_minimal_antichain:
  "nativeMinimal e i \<Longrightarrow> nativeMinimal e j \<Longrightarrow>
    \<not> tranclp edge i j \<and> \<not> tranclp edge j i"
  using bound.minimal_antichain by (simp add: minimal_exact)

end

ML \<open>
val roots = @{thms matching_differential.input_unique matching_differential.input_same_selected_law matching_differential.no_input_outside matching_differential.condition_exact matching_differential.law_ready_exact matching_differential.minimal_exact matching_differential.failure_exact matching_differential.native_failure_cover matching_differential.native_minimal_antichain};
if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
\<close>
end
