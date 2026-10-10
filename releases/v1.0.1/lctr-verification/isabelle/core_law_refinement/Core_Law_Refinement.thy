theory Core_Law_Refinement
  imports "LCTR_Core_Law_Countercases.Core_Law_Countercases"
    "LCTR_Core_Refinement_Forest.Core_Refinement_Forest"
begin

fun case_set :: "law_node \<Rightarrow> bool set" where
  "case_set Law1 = UNIV" | "case_set Law2 = {False}" |
  "case_set Law3 = UNIV" | "case_set Law4 = UNIV" | "case_set Law5 = UNIV"
fun occurrence where
  "occurrence d Law1 j = (if j then out_eval d else empty_time d)" |
  "occurrence d Law2 j = gen_conflict d" |
  "occurrence d Law3 j = (if j then alt_output d else empty_fiber d)" |
  "occurrence d Law4 j = (if j then gain d else loss d)" |
  "occurrence d Law5 j = (if j then inadmissible_common d else empty_common d)"
definition pure_case where "pure_case d i j \<longleftrightarrow>
  occurrence d i j \<and> (\<forall>k\<in>case_set i. k \<noteq> j \<longrightarrow> \<not> occurrence d i k)"
fun remainder_case where
  "remainder_case d Law1 = (empty_time d \<and> out_eval d)" |
  "remainder_case d Law2 = off_gen_conflict d" |
  "remainder_case d Law3 = (empty_fiber d \<and> alt_output d)" |
  "remainder_case d Law4 = (loss d \<and> gain d)" |
  "remainder_case d Law5 = False"
fun cover_case where
  "cover_case d Law1 = pure_pair (empty_time d) (out_eval d)" |
  "cover_case d Law2 = gen_conflict d" |
  "cover_case d Law3 = pure_pair (empty_fiber d) (alt_output d)" |
  "cover_case d Law4 = pure_pair (loss d) (gain d)" |
  "cover_case d Law5 = pure_pair (empty_common d) (inadmissible_common d)"
definition raw_parent where "raw_parent d i \<longleftrightarrow>
  Core_Law_Failure.ancestors_hold (condition d) i \<and> \<not> condition d i"

lemma pure_cases_exclusive:
  "j \<in> case_set i \<Longrightarrow> k \<in> case_set i \<Longrightarrow> j \<noteq> k \<Longrightarrow>
   \<not> (pure_case d i j \<and> pure_case d i k)"
  unfolding pure_case_def by blast
lemma pure_cover_formula:
  "(\<exists>j\<in>case_set i. pure_case d i j) \<longleftrightarrow> cover_case d i"
  by (cases i; auto simp: pure_case_def pure_pair_def all_bool_eq ex_bool_eq)
lemma native_remainder_formula:
  assumes wf: "well_typed_family d" and hp: "raw_parent d i"
  shows "(\<not> (\<exists>j\<in>case_set i. pure_case d i j)) \<longleftrightarrow> remainder_case d i"
proof -
  have eq: "(\<not> cover_case d i) \<longleftrightarrow> remainder_case d i"
  proof (cases i)
    case Law1
    have hn: "\<not> K1 d" using hp Law1 by (auto simp: raw_parent_def)
    have occ: "empty_time d \<or> out_eval d" using condition1_countercases[of d] hn by simp
    show ?thesis using pair_remainder[OF occ] Law1 by simp
  next
    case Law2
    have hn: "\<not> K2 d" using hp Law2 by (auto simp: raw_parent_def)
    show ?thesis using condition2_remainder[OF wf hn] Law2 by simp
  next
    case Law3
    have h1: "K1 d" and hn: "\<not> K3 d" using hp Law3
      by (auto simp: raw_parent_def Core_Law_Failure.ancestors_hold_def
          Core_Law_Failure.ancestor_def Core_Law_Failure.edge_def)
    have occ: "empty_fiber d \<or> alt_output d" using condition3_countercases[OF h1] hn by simp
    show ?thesis using pair_remainder[OF occ] Law3 by simp
  next
    case Law4
    have hn: "\<not> K4 d" using hp Law4 by (auto simp: raw_parent_def)
    show ?thesis using condition4_remainder[OF wf hn] Law4 by simp
  next
    case Law5
    have h3: "K3 d" and hn: "\<not> K5 d" using hp Law5
      by (auto simp: raw_parent_def Core_Law_Failure.ancestors_hold_def
          Core_Law_Failure.ancestor_def Core_Law_Failure.edge_def)
    have p: "pure_pair (empty_common d) (inadmissible_common d)"
      using condition135_remainders[of d] h3 hn by blast
    show ?thesis using p Law5 by simp
  qed
  show ?thesis using eq by (simp only: pure_cover_formula)
qed

locale law_refinement =
  fixes selected :: "'e set" and evaluation :: "'e set"
    and datum :: "'e \<Rightarrow> ('t,'a,'x,'y) law_family"
  assumes typed: "\<And>e. e \<in> selected \<Longrightarrow> well_typed_family (datum e)"
begin
definition total_condition where "total_condition e i \<longleftrightarrow> e \<in> selected \<and> condition (datum e) i"
definition selected_minimal where "selected_minimal e i \<longleftrightarrow> e \<in> selected \<and>
  Core_Law_Failure.ancestors_hold (total_condition e) i \<and> \<not> total_condition e i"
definition parent where "parent i = {e\<in>evaluation. selected_minimal e i}"
definition selected_pure where "selected_pure e i j \<longleftrightarrow> e \<in> selected \<and> pure_case (datum e) i j"
definition child where "child i j = {e\<in>parent i. selected_pure e i j}"

lemma selected_parent_exact:
  "e \<in> selected \<Longrightarrow> (selected_minimal e i \<longleftrightarrow> raw_parent (datum e) i)"
  by (simp add: selected_minimal_def raw_parent_def total_condition_def Core_Law_Failure.ancestors_hold_def)
lemma parent_subset_evaluation: "parent i \<subseteq> evaluation"
  by (auto simp: parent_def)
lemma child_subset_parent: "child i j \<subseteq> parent i"
  by (auto simp: child_def)
lemma children_pairwise_disjoint:
  "j \<in> case_set i \<Longrightarrow> k \<in> case_set i \<Longrightarrow> j \<noteq> k \<Longrightarrow> child i j \<inter> child i k = {}"
  using pure_cases_exclusive[of j i k]
  unfolding child_def selected_pure_def by blast
lemma parent_to_native:
  "e \<in> selected \<Longrightarrow> e \<in> parent i \<Longrightarrow> raw_parent (datum e) i"
  using selected_parent_exact[of e i] by (simp add: parent_def)

sublocale R: two_level_regions UNIV case_set "\<lambda>_ _. {}::unit set"
  parent child "\<lambda>_ _ _. {}"
  by unfold_locales (auto intro: child_subset_parent[THEN subsetD])

lemma covered_membership:
  "e \<in> selected \<Longrightarrow> (e \<in> R.F.covered (Root i) \<longleftrightarrow>
    e \<in> parent i \<and> (\<exists>j\<in>case_set i. pure_case (datum e) i j))"
  by (auto simp: R.F.covered_def child_def selected_pure_def)
lemma unrefined_exact:
  assumes e: "e \<in> selected" and hp: "e \<in> parent i"
  shows "e \<in> R.F.unrefined (Root i) \<longleftrightarrow> remainder_case (datum e) i"
  using native_remainder_formula[OF typed[OF e] parent_to_native[OF e hp]]
  by (simp add: R.F.unrefined_def covered_membership[OF e] hp)
lemma root_decomposition:
  "parent i = R.F.covered (Root i) \<union> R.F.unrefined (Root i) \<and>
   R.F.covered (Root i) \<inter> R.F.unrefined (Root i) = {}"
  using R.F.node_decomposition[of "Root i"] by simp
lemma root_unrefined_subset: "R.F.unrefined (Root i) \<subseteq> parent i"
  by (auto simp: R.F.unrefined_def)
lemma node5_unrefined_empty: "R.F.unrefined (Root Law5) = {}"
proof -
  have impossible: "False" if e: "e \<in> R.F.unrefined (Root Law5)" for e
  proof -
    have hp: "e \<in> parent Law5" using root_unrefined_subset e by auto
    have sel: "e \<in> selected" using hp by (simp add: parent_def selected_minimal_def)
    have "remainder_case (datum e) Law5" using unrefined_exact[OF sel hp] e by simp
    then show False by simp
  qed
  show ?thesis using impossible by auto
qed
lemma node5_covered_all: "R.F.covered (Root Law5) = parent Law5"
  using root_decomposition[of Law5] by (simp add: node5_unrefined_empty)
lemma first_level_terminal:
  "R.F.covered (First i j) = {} \<and> R.F.unrefined (First i j) = child i j"
  by (simp add: R.F.covered_def R.F.unrefined_def)
lemma root_snapshot_monotonicity:
  fixes embed :: "'j \<Rightarrow> 'k" and r0 :: "'j \<Rightarrow> 'e set" and r1 :: "'k \<Rightarrow> 'e set"
  assumes same: "\<And>j. r0 j = r1 (embed j)"
  shows "(\<Union>j. r0 j) \<subseteq> (\<Union>j. r1 j) \<and>
    parent i - (\<Union>j. r1 j) \<subseteq> parent i - (\<Union>j. r0 j)"
proof (rule Core_Refinement_Forest.snapshot_monotonicity[where I=UNIV and J=UNIV and embed=embed and r=r0 and s=r1])
  fix j :: 'j assume "j \<in> UNIV"
  show "embed j \<in> UNIV" by simp
next
  fix j :: 'j assume "j \<in> UNIV"
  show "r0 j = r1 (embed j)" by (rule same)
qed
end

ML \<open>
val roots = @{thms pure_cases_exclusive pure_cover_formula native_remainder_formula
  law_refinement.parent_subset_evaluation law_refinement.child_subset_parent
  law_refinement.children_pairwise_disjoint law_refinement.parent_to_native
  law_refinement.covered_membership law_refinement.unrefined_exact
  law_refinement.root_decomposition law_refinement.root_unrefined_subset
  law_refinement.node5_unrefined_empty law_refinement.node5_covered_all
  law_refinement.first_level_terminal law_refinement.root_snapshot_monotonicity};
val _ = if null (Thm_Deps.all_oracles roots) then () else error "Unexpected oracle dependency";
val _ = writeln ("LCTR_CHECKED_ROOTS=" ^ string_of_int (length roots));
\<close>
end
